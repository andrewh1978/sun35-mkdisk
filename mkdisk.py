#!/usr/bin/env python3
"""
sunos35_diskbuilder.py -- build a bootable SunOS 3.5 (Sun-3) SCSI disk image.

Takes the "sun3_sunos3.5" install set (the .tar files that normally go onto the
five QIC-24 install tapes) and produces a raw disk image that can be used
directly as a ZuluSCSI / BlueSCSI / SCSI2SD hard-disk image:

    sector 0        Sun disk label (dk_label, magic 0xDABE)
    sectors 1-15    first-stage boot block (/usr/mdec/bootsd), as installboot does
    partition a     /      4.2BSD filesystem (root + pub files + /dev)
    partition b     swap
    partition c     whole disk
    partition g     /usr   4.2BSD filesystem (usr + every optional software group)

Everything is derived from the SunOS 3.5 kernel headers on the media
(sys/sun/dklabel.h, sys/ufs/fs.h, sys/ufs/inode.h, sys/ufs/fsdir.h) and from the
miniroot filesystem image on the same media, which is a genuine Sun mkfs
product used as a format reference.

Usage:
    python3 sunos35_diskbuilder.py sunos35_tar.bz2  sunos35.img
    python3 sunos35_diskbuilder.py ./sun3_sunos3.5/ sunos35.img --usr-mb 400

No third-party modules are needed (Python 3.8+).  If "unicorn" is installed
(pip install unicorn) the script also runs the genuine /boot program from the tape
against the finished image in an emulator and tells you whether it can load /vmunix.
"""
import argparse, io, math, os, struct, sys, tarfile, time

# --------------------------------------------------------------------------
# constants taken from the SunOS 3.5 headers
# --------------------------------------------------------------------------
SECTOR = 512
BSIZE, FSIZE = 8192, 1024
FRAG = BSIZE // FSIZE          # 8
NSPF = FSIZE // SECTOR         # 2 sectors per frag
NSPB = NSPF * FRAG             # 16 sectors per block
INOPB = BSIZE // 128           # 64
NINDIR = BSIZE // 4            # 2048
NRPOS = 8
MAXIPG = 2048
MAXCPG = 32
SBLKNO, CBLKNO = 16, 24        # frags (BBSIZE+SBSIZE, then +SBSIZE)
SBSIZE_ON_DISK = 2048          # fs_sbsize used by Sun mkfs for this layout
FS_MAGIC, CG_MAGIC = 0x011954, 0x090255
ROOTINO = 2
DKL_MAGIC = 0xDABE

IFMT, IFIFO, IFCHR, IFDIR, IFBLK, IFREG, IFLNK, IFSOCK = (
    0o170000, 0o010000, 0o020000, 0o040000, 0o060000, 0o100000, 0o120000, 0o140000)


def fragroundup(n):
    return (n + FSIZE - 1) // FSIZE * FSIZE


def roundup(n, m):
    return (n + m - 1) // m * m


class NoSpace(Exception):
    pass


# --------------------------------------------------------------------------
# in-memory file tree
# --------------------------------------------------------------------------
class Node:
    __slots__ = ("type", "mode", "uid", "gid", "mtime", "data", "rdev",
                 "children", "ino", "parent")

    def __init__(self, type_, mode=0o755, uid=0, gid=0, mtime=0, data=b"", rdev=0):
        self.type = type_            # 'd' dir, 'f' file, 'l' symlink, 'c' chr, 'b' blk
        self.mode = mode & 0o7777
        self.uid, self.gid, self.mtime = uid, gid, mtime
        self.data = data
        self.rdev = rdev
        self.children = {} if type_ == "d" else None
        self.ino = 0
        self.parent = None

    def ifmt(self):
        return {"d": IFDIR, "f": IFREG, "l": IFLNK, "c": IFCHR, "b": IFBLK}[self.type]


class Tree:
    def __init__(self, now):
        self.now = now
        self.root = Node("d", 0o755, 0, 0, now)
        self.root.parent = self.root

    @staticmethod
    def split(path):
        return [p for p in path.split("/") if p not in ("", ".")]

    def lookup(self, path):
        n = self.root
        for p in self.split(path):
            if n.type != "d" or p not in n.children:
                return None
            n = n.children[p]
        return n

    def mkdirs(self, parts):
        n = self.root
        for p in parts:
            c = n.children.get(p)
            if c is None:
                c = Node("d", 0o755, 0, 0, self.now)
                c.parent = n
                n.children[p] = c
            n = c
        return n

    def add(self, path, node):
        parts = self.split(path)
        if not parts:
            return self.root
        par = self.mkdirs(parts[:-1])
        old = par.children.get(parts[-1])
        if node.type == "d" and old is not None and old.type == "d":
            old.mode, old.uid, old.gid, old.mtime = node.mode, node.uid, node.gid, node.mtime
            return old
        node.parent = par
        par.children[parts[-1]] = node
        return node

    def add_tar(self, tf, log=None):
        count = 0
        for m in tf:
            name = m.name
            if m.isdir():
                self.add(name, Node("d", m.mode, m.uid, m.gid, m.mtime))
            elif m.isreg():
                self.add(name, Node("f", m.mode, m.uid, m.gid, m.mtime,
                                    tf.extractfile(m).read()))
            elif m.issym():
                self.add(name, Node("l", m.mode, m.uid, m.gid, m.mtime,
                                    m.linkname.encode("latin1")))
            elif m.islnk():
                tgt = self.lookup(m.linkname)
                if tgt is None:
                    raise ValueError("hard link to unknown file: %s -> %s" % (name, m.linkname))
                parts = self.split(name)
                par = self.mkdirs(parts[:-1])
                par.children[parts[-1]] = tgt       # same Node object == hard link
            elif m.ischr() or m.isblk():
                self.add(name, Node("c" if m.ischr() else "b", m.mode, m.uid, m.gid, m.mtime,
                                    rdev=(m.devmajor << 8) | m.devminor))
            else:
                raise ValueError("unsupported tar member type: %s" % name)
            count += 1
        return count

    def put_file(self, path, data, mode=0o644, uid=0, gid=0):
        if isinstance(data, str):
            data = data.encode("latin1")
        return self.add(path, Node("f", mode, uid, gid, self.now, data))


# --------------------------------------------------------------------------
# the filesystem writer (SunOS 3.5 / 4.2BSD fast file system, big-endian)
# --------------------------------------------------------------------------
class UFS:
    def __init__(self, img, base_sector, nsectors, nhead, nsect, cpg=16, ipg=1024,
                 minfree=10, rotdelay=0, rps=60, mnt="", now=None):
        self.img = img
        self.base = base_sector * SECTOR
        self.nhead, self.nsect = nhead, nsect
        self.spc = nhead * nsect
        if nsectors % self.spc:
            raise ValueError("partition must be a whole number of cylinders")
        self.ncyl = nsectors // self.spc
        self.size = nsectors // NSPF                    # frags
        self.cpg, self.ipg = cpg, ipg
        if cpg > MAXCPG or ipg > MAXIPG or ipg % INOPB:
            raise ValueError("bad cpg/ipg")
        self.fpg = cpg * self.spc // NSPF
        if self.fpg % FRAG:
            raise ValueError("cylinder group is not a multiple of the block size")
        self.ncg = -(-self.ncyl // cpg)
        self.minfree, self.rotdelay, self.rps = minfree, rotdelay, rps
        self.mnt = mnt
        self.now = now or int(time.time())
        # cylinder group layout
        self.cgsize = fragroundup(986 + (self.fpg + 7) // 8)
        if self.cgsize > BSIZE:
            raise ValueError("cylinder group too large for one block (reduce cpg)")
        self.sblkno, self.cblkno = SBLKNO, CBLKNO
        self.iblkno = self.cblkno + roundup(-(-self.cgsize // FSIZE), FRAG)
        self.dblkno = self.iblkno + self.ipg // INOPB * FRAG
        self.cgoffset = roundup(-(-self.nsect // NSPF), FRAG)
        m = -1
        i = nhead
        while i > 1:
            m <<= 1
            i >>= 1
        self.cgmask = m
        self.cssize = fragroundup(self.ncg * 16)
        self.csfrags = self.cssize // FSIZE
        # rotational layout tables
        g = math.gcd(NSPB, self.spc)
        self.cpc = NSPB // g
        if self.cpc > MAXCPG:
            raise ValueError("fs_cpc too large")
        self.postbl = [[-1] * NRPOS for _ in range(self.cpc)]
        self.rotbl = bytearray(self.cpc * self.spc // NSPB)
        last = {}
        for i in range(len(self.rotbl)):
            bno = i * FRAG
            cyl = bno * NSPF // self.spc
            pos = bno * NSPF % self.spc % self.nsect * NRPOS // self.nsect
            key = (cyl, pos)
            if key in last:
                self.rotbl[last[key]] = i - last[key]
            else:
                self.postbl[cyl][pos] = i
            last[key] = i
        # per-cg bookkeeping
        self.ndblk, self.fm, self.iused, self.ndir = [], [], [], []
        self.nifree, self.irotor, self.arotor = [], [], []
        self.exhausted = []
        self.partial = []
        self.dsize = 0
        for c in range(self.ncg):
            cbase = c * self.fpg
            nd = min(self.fpg, self.size - cbase)
            self.ndblk.append(nd)
            f = bytearray(b"\x01") * nd
            dmin = self.cgdmin(c) - cbase
            if c == 0:
                lo, hi = 0, dmin + self.csfrags
            else:
                lo, hi = self.cgsblock(c) - cbase, dmin
            if hi > nd:
                raise ValueError("cylinder group %d too small" % c)
            f[lo:hi] = b"\x00" * (hi - lo)
            self.fm.append(f)
            self.dsize += nd - (hi - lo)
            iu = bytearray(self.ipg)
            self.iused.append(iu)
            self.ndir.append(0)
            self.nifree.append(self.ipg)
            self.irotor.append(0)
            self.arotor.append(0)
            self.exhausted.append(False)
            part = set()
            for b in range(0, nd - nd % FRAG, FRAG):
                s = sum(f[b:b + FRAG])
                if 0 < s < FRAG:
                    part.add(b)
            self.partial.append(part)
        for i in range(ROOTINO):                 # inodes 0 and 1 are reserved
            self.iused[0][i] = 1
            self.nifree[0] -= 1

    # ---- geometry helpers -------------------------------------------------
    def cgbase(self, c):
        return c * self.fpg

    def cgstart(self, c):
        return self.cgbase(c) + self.cgoffset * (c & ~self.cgmask)

    def cgsblock(self, c):
        return self.cgstart(c) + self.sblkno

    def cgtod(self, c):
        return self.cgstart(c) + self.cblkno

    def cgimin(self, c):
        return self.cgstart(c) + self.iblkno

    def cgdmin(self, c):
        return self.cgstart(c) + self.dblkno

    def _w(self, frag, data):
        o = self.base + frag * FSIZE
        self.img[o:o + len(data)] = data

    # ---- allocation ---------------------------------------------------------
    def _take_block(self, c, idx):
        self.fm[c][idx:idx + FRAG] = b"\x00" * FRAG
        return c * self.fpg + idx

    def alloc_block(self, cgpref=0, pref=None):
        ones = b"\x01" * FRAG
        if pref is not None:
            c, idx = divmod(pref, self.fpg)
            if (c < self.ncg and idx % FRAG == 0 and idx + FRAG <= self.ndblk[c]
                    and self.fm[c][idx:idx + FRAG] == ones):
                self.arotor[c] = idx + FRAG
                return self._take_block(c, idx)
            cgpref = c if c < self.ncg else cgpref
        for k in range(self.ncg):
            c = (cgpref + k) % self.ncg
            if self.exhausted[c]:
                continue
            n = self.ndblk[c] - self.ndblk[c] % FRAG
            start = self.arotor[c] // FRAG * FRAG
            f = self.fm[c]
            for rng in (range(start, n, FRAG), range(0, start, FRAG)):
                for idx in rng:
                    if f[idx:idx + FRAG] == ones:
                        self.arotor[c] = idx + FRAG
                        return self._take_block(c, idx)
            self.exhausted[c] = True
        raise NoSpace("filesystem full")

    def alloc_frags(self, n, cgpref=0):
        """allocate n (< FRAG) contiguous fragments inside one block"""
        if n == FRAG:
            return self.alloc_block(cgpref)
        for k in range(self.ncg):
            c = (cgpref + k) % self.ncg
            f = self.fm[c]
            best = None
            for b in sorted(self.partial[c]):
                i = 0
                while i < FRAG:
                    if f[b + i]:
                        j = i
                        while j < FRAG and f[b + j]:
                            j += 1
                        if j - i >= n and (best is None or j - i < best[0]):
                            best = (j - i, b + i)
                        i = j
                    else:
                        i += 1
                if best and best[0] == n:
                    break
            if best:
                pos = best[1]
                f[pos:pos + n] = b"\x00" * n
                b = pos - pos % FRAG
                if sum(f[b:b + FRAG]) == 0:
                    self.partial[c].discard(b)
                return c * self.fpg + pos
        blk = self.alloc_block(cgpref)
        c, idx = divmod(blk, self.fpg)
        self.fm[c][idx + n:idx + FRAG] = b"\x01" * (FRAG - n)
        self.partial[c].add(idx)
        return blk

    def alloc_inode(self, cgpref, isdir=False):
        for k in range(self.ncg):
            c = (cgpref + k) % self.ncg
            if self.nifree[c] <= 0:
                continue
            iu = self.iused[c]
            i = iu.find(b"\x00", self.irotor[c])
            if i < 0:
                i = iu.find(b"\x00")
            iu[i] = 1
            self.irotor[c] = i
            self.nifree[c] -= 1
            if isdir:
                self.ndir[c] += 1
            return c * self.ipg + i
        raise NoSpace("out of inodes")

    def dirpref(self):
        avg = sum(self.nifree) // self.ncg
        best = None
        for c in range(self.ncg):
            if self.nifree[c] >= avg and (best is None or self.ndir[c] < self.ndir[best]):
                best = c
        return best

    # ---- inode I/O --------------------------------------------------------------
    def put_inode(self, n, mode, nlink, uid, gid, size, atime, mtime, ctime,
                  db, ib, sectors):
        c, i = divmod(n, self.ipg)
        frag = self.cgimin(c) + (i // INOPB) * FRAG
        off = self.base + frag * FSIZE + (i % INOPB) * 128
        db = list(db) + [0] * (12 - len(db))
        ib = list(ib) + [0] * (3 - len(ib))
        rec = struct.pack(">Hhhh", mode, nlink, _s16(uid), _s16(gid))
        rec += struct.pack(">Q", size)
        rec += struct.pack(">6l", atime, 0, mtime, 0, ctime, 0)
        rec += struct.pack(">12l", *db) + struct.pack(">3l", *ib)
        rec += struct.pack(">3l", 0, sectors, 0) + b"\0" * 16
        assert len(rec) == 128
        self.img[off:off + 128] = rec

    # ---- file data ------------------------------------------------------------------
    def write_data(self, data, cgpref):
        """allocate + write file data. returns (db[12], ib[3], sectors)"""
        size = len(data)
        nb = -(-size // BSIZE)
        if nb > 12 + NINDIR + NINDIR * NINDIR:
            raise NoSpace("file too large")
        db = [0] * 12
        ib = [0, 0, 0]
        ptrs = []
        frags_used = 0
        last = None
        ind_blocks = []                 # (frag, [pointers])
        for l in range(nb):
            if l < 12 and l == nb - 1 and size % BSIZE:
                nf = -(-(size % BSIZE) // FSIZE)
            else:
                nf = FRAG
            if l == 12:
                ib[0] = self.alloc_block(cgpref, None if last is None else last + FRAG)
                frags_used += FRAG
                last = ib[0]
                ind_blocks.append((ib[0], ptrs))
            if l >= 12 + NINDIR:
                raise NoSpace("double indirect not needed here")
            if nf == FRAG:
                fb = self.alloc_block(cgpref, None if last is None else last + FRAG)
            else:
                fb = self.alloc_frags(nf, cgpref)
            frags_used += nf
            last = fb + nf - FRAG if nf < FRAG else fb
            chunk = data[l * BSIZE:(l + 1) * BSIZE]
            self._w(fb, chunk)
            if l < 12:
                db[l] = fb
            else:
                ptrs.append(fb)
            cgpref = fb // self.fpg
        for frag, p in ind_blocks:
            self._w(frag, struct.pack(">%dl" % len(p), *p))
        return db, ib, frags_used * NSPF

    # ---- directories ---------------------------------------------------------------------
    @staticmethod
    def dir_bytes(entries):
        chunks, cur, used = [], [], 0

        def flush():
            nonlocal cur, used
            if not cur:
                return
            out = bytearray()
            for k, (ino, nm, rl) in enumerate(cur):
                if k == len(cur) - 1:
                    rl += SECTOR - used
                out += struct.pack(">LHH", ino, rl, len(nm)) + nm + b"\0" * (rl - 8 - len(nm))
            assert len(out) == SECTOR
            chunks.append(bytes(out))
            cur, used = [], 0

        for ino, name in entries:
            nm = name.encode("latin1")
            rl = 8 + ((len(nm) + 1 + 3) & ~3)
            if used + rl > SECTOR:
                flush()
            cur.append((ino, nm, rl))
            used += rl
        flush()
        return b"".join(chunks)

    # ---- populate from a Tree ---------------------------------------------------------------
    def populate(self, tree, lost_found=True):
        root = tree.root
        if lost_found and "lost+found" not in root.children:
            lf = Node("d", 0o755, 0, 0, self.now)
            lf.parent = root
            new = {"lost+found": lf}
            new.update(root.children)
            root.children = new
        # pass 1: inode numbers
        seen = set()
        links = {}

        def assign(node, cgpref):
            if id(node) in seen:
                links[id(node)] += 1
                return
            seen.add(id(node))
            links[id(node)] = 1
            if node.type == "d":
                if node is root:
                    node.ino = self.alloc_inode(0, True)
                    assert node.ino == ROOTINO
                else:
                    c = 0 if (node.parent is root and node is root.children.get("lost+found")) \
                        else self.dirpref()
                    node.ino = self.alloc_inode(c, True)
                c = node.ino // self.ipg
                for nm, ch in node.children.items():
                    assign(ch, c)
            else:
                node.ino = self.alloc_inode(cgpref)

        assign(root, 0)
        # pass 2: data, directory contents, inodes
        done = set()

        def emit(node, parent_ino):
            if id(node) in done:
                return
            done.add(id(node))
            c = node.ino // self.ipg
            now = self.now
            if node.type == "d":
                ents = [(node.ino, "."), (parent_ino, "..")]
                for nm, ch in node.children.items():
                    ents.append((ch.ino, nm))
                if node is root.children.get("lost+found") and node.parent is root:
                    chunk0 = self.dir_bytes(ents[:2])   # like Sun mkfs: one 8K block
                    empty = struct.pack(">LHH", 0, SECTOR, 0) + b"\0" * (SECTOR - 8)
                    data = chunk0 + empty * (BSIZE // SECTOR - 1)
                else:
                    data = self.dir_bytes(ents)
                db, ib, sect = self.write_data(data, c)
                nsub = sum(1 for ch in node.children.values() if ch.type == "d")
                self.put_inode(node.ino, IFDIR | node.mode, 2 + nsub, node.uid, node.gid,
                               len(data), node.mtime, node.mtime, now, db, ib, sect)
                for nm, ch in node.children.items():
                    emit(ch, node.ino)
            elif node.type in ("f", "l"):
                db, ib, sect = self.write_data(node.data, c)
                self.put_inode(node.ino, node.ifmt() | node.mode, links[id(node)], node.uid,
                               node.gid, len(node.data), node.mtime, node.mtime, now,
                               db, ib, sect)
            else:                                    # device special
                self.put_inode(node.ino, node.ifmt() | node.mode, links[id(node)], node.uid,
                               node.gid, 0, node.mtime, node.mtime, now,
                               [node.rdev], [], 0)

        emit(root, ROOTINO)

    # ---- finish: cylinder groups, summary area, superblock ------------------------------------------
    def finalize(self):
        tot = [0, 0, 0, 0]          # ndir nbfree nifree nffree
        cs = []
        cgblocks = []
        for c in range(self.ncg):
            f = self.fm[c]
            nd = self.ndblk[c]
            nb = nf = 0
            frsum = [0] * 8
            btot = [0] * MAXCPG
            bpos = [[0] * NRPOS for _ in range(MAXCPG)]
            for b in range(0, nd - nd % FRAG, FRAG):
                blk = f[b:b + FRAG]
                s = sum(blk)
                if s == FRAG:
                    nb += 1
                    cyl = b * NSPF // self.spc
                    pos = b * NSPF % self.spc % self.nsect * NRPOS // self.nsect
                    btot[cyl] += 1
                    bpos[cyl][pos] += 1
                elif s:
                    nf += s
                    i = 0
                    while i < FRAG:
                        if blk[i]:
                            j = i
                            while j < FRAG and blk[j]:
                                j += 1
                            frsum[j - i] += 1
                            i = j
                        else:
                            i += 1
            ni = self.nifree[c]
            ncyl_c = self.cpg if c < self.ncg - 1 else self.ncyl - self.cpg * (self.ncg - 1)
            cs.append((self.ndir[c], nb, ni, nf))
            for k, v in enumerate((self.ndir[c], nb, ni, nf)):
                tot[k] += v
            # (cg_niblk holds the per-group inode count in this release)
            hdr = struct.pack(">lllLhhl", 0, 0, self.now, c, ncyl_c, self.ipg, nd)
            hdr += struct.pack(">4l", self.ndir[c], nb, ni, nf)
            hdr += struct.pack(">3l", 0, 0, 0)
            hdr += struct.pack(">8l", *frsum)
            hdr += struct.pack(">32l", *btot)
            for row in bpos:
                hdr += struct.pack(">8h", *row)
            iu = bytearray(MAXIPG // 8)
            for i in range(self.ipg):
                if self.iused[c][i]:
                    iu[i // 8] |= 1 << (i % 8)
            hdr += bytes(iu) + struct.pack(">l", CG_MAGIC)
            fmap = bytearray((self.fpg + 7) // 8)
            for i in range(nd):
                if f[i]:
                    fmap[i // 8] |= 1 << (i % 8)
            blob = hdr + bytes(fmap)
            assert len(hdr) == 984
            blob = blob.ljust(self.cgsize, b"\0")
            cgblocks.append(blob)
        sb = self.pack_sb(tot)
        # write cylinder groups, summary info, super blocks
        for c in range(self.ncg):
            self._w(self.cgtod(c), cgblocks[c])
            self._w(self.cgsblock(c), sb)
        self._w(self.csaddr(), b"".join(struct.pack(">4l", *x) for x in cs))
        self.img[self.base + 8192:self.base + 8192 + len(sb)] = sb
        return tot

    def csaddr(self):
        return self.cgdmin(0)

    def pack_sb(self, tot):
        v = [0, 0, self.sblkno, self.cblkno, self.iblkno, self.dblkno, self.cgoffset,
             self.cgmask, self.now, self.size, self.dsize, self.ncg, BSIZE, FSIZE, FRAG,
             self.minfree, self.rotdelay, self.rps, -BSIZE, -FSIZE, 13, 10, 1,
             self.fpg // FRAG, 3, 1, SBSIZE_ON_DISK, -(BSIZE // 16), 9, NINDIR, INOPB, NSPF,
             0, 0, 0, 0, 0, 0, self.csaddr(), self.cssize, self.cgsize, self.nhead,
             self.nsect, self.spc, self.ncyl, self.cpg, self.ipg, self.fpg,
             tot[0], tot[1], tot[2], tot[3]]
        assert len(v) == 52
        sb = struct.pack(">52l", *v)
        sb += b"\0\0\0\0"                                 # fmod clean ronly flags
        sb += self.mnt.encode().ljust(512, b"\0")
        sb += struct.pack(">l", 0) + b"\0" * 128          # cgrotor, csp[]
        sb += struct.pack(">l", self.cpc)
        pb = b""
        for i in range(MAXCPG):
            row = self.postbl[i] if i < self.cpc else [-1] * NRPOS
            pb += struct.pack(">8h", *row)
        sb += pb + struct.pack(">l", FS_MAGIC) + bytes(self.rotbl)
        assert sb.index(struct.pack(">l", FS_MAGIC)) == 1372
        return sb.ljust(SBSIZE_ON_DISK, b"\0")


def _s16(x):
    x &= 0xFFFF
    return x - 0x10000 if x >= 0x8000 else x


# --------------------------------------------------------------------------
# Sun disk label
# --------------------------------------------------------------------------
def make_label(ascii_label, ncyl, acyl, nhead, nsect, parts):
    """parts: dict letter -> (start_cylinder, nblocks)"""
    lab = bytearray(512)
    lab[0:len(ascii_label)] = ascii_label.encode("ascii")
    struct.pack_into(">10H", lab, 424, 0, 0, 0, 1, ncyl, acyl, nhead, nsect, 0, 0)
    for i, ch in enumerate("abcdefgh"):
        cyl, nblk = parts.get(ch, (0, 0))
        struct.pack_into(">ll", lab, 444 + 8 * i, cyl, nblk)
    struct.pack_into(">H", lab, 508, DKL_MAGIC)
    x = 0
    for i in range(0, 510, 2):
        x ^= struct.unpack_from(">H", lab, i)[0]
    struct.pack_into(">H", lab, 510, x)
    return bytes(lab)


# --------------------------------------------------------------------------
# device nodes (what /dev/MAKEDEV would create)
# --------------------------------------------------------------------------
def add_devices(tree, now):
    dev = tree.mkdirs(["dev"])

    def mk(name, kind, major, minor, mode):
        n = Node(kind, mode, 0, 0, now, rdev=(major << 8) | minor)
        n.parent = dev
        dev.children[name] = n
        return n

    for name, major, minor, mode in [
        ("console", 0, 0, 0o622), ("tty", 2, 0, 0o666), ("mem", 3, 0, 0o644),
        ("kmem", 3, 1, 0o644), ("null", 3, 2, 0o666), ("mbmem", 3, 3, 0o600),
        ("mbio", 3, 4, 0o600), ("vme16d16", 3, 5, 0o600), ("vme24d16", 3, 6, 0o600),
        ("vme32d16", 3, 7, 0o600), ("vme16d32", 3, 8, 0o600), ("vme24d32", 3, 9, 0o600),
        ("vme32d32", 3, 10, 0o600), ("eeprom", 3, 11, 0o644), ("drum", 7, 0, 0o644),
        ("ttya", 12, 0, 0o666), ("ttyb", 12, 1, 0o666), ("mouse", 13, 0, 0o666),
        ("fb", 22, 0, 0o666), ("ropc", 23, 0, 0o666), ("kbd", 29, 0, 0o666)]:
        mk(name, "c", major, minor, mode)
    for ln, tgt in (("vme16", "vme16d16"), ("vme24", "vme24d16"), ("vme32", "vme32d32")):
        dev.children[ln] = dev.children[tgt]            # hard links, as MAKEDEV does
    for unit in (0, 1):                                  # SCSI disks
        for k, ch in enumerate("abcdefgh"):
            mk("sd%d%s" % (unit, ch), "b", 7, unit * 8 + k, 0o600)
            mk("rsd%d%s" % (unit, ch), "c", 17, unit * 8 + k, 0o600)
    for unit in (0, 1):                                  # SCSI tapes
        mk("rst%d" % unit, "c", 18, unit, 0o666)
        mk("rst%d" % (unit + 8), "c", 18, unit + 8, 0o666)
        mk("nrst%d" % unit, "c", 18, unit + 4, 0o666)
        mk("nrst%d" % (unit + 8), "c", 18, unit + 12, 0o666)
    mk("bwtwo0", "c", 27, 0, 0o666)
    mk("cgtwo0", "c", 31, 0, 0o666)
    mk("cgfour0", "c", 39, 0, 0o666)
    for k in range(4):                                   # on-board serial / SCSI UARTs
        mk("ttys%d" % k, "c", 12, 4 + k, 0o600)
        mk("ttyt%d" % k, "c", 12, 8 + k, 0o600)
    for cls, (off, nm) in enumerate(((0, "p"), (16, "q"), (32, "r"))):   # ptys
        for i in range(16):
            mk("tty%s%x" % (nm, i), "c", 20, off + i, 0o666)
            mk("pty%s%x" % (nm, i), "c", 21, off + i, 0o666)
    for i in range(128):                                 # windows
        mk("win%d" % i, "c", 15, i, 0o666)



# --------------------------------------------------------------------------
# optional self-test: run the genuine SunOS 3.5 /boot program (68020 code) under the
# Unicorn CPU emulator against the finished image.  The PROM, the MMU and the SCSI
# controller are faked; everything else -- the boot program's label check, partition
# handling, superblock read, directory lookup, block mapping and a.out loader -- is the
# real code from your tape.  PASS means /boot found /vmunix on sd(0,0,0), read all of it
# and would have jumped to the kernel.  (pip install unicorn)
# --------------------------------------------------------------------------
def verify_boot(img_path, boot_bin, vmunix_bin, devstr="sd(0,0,0)", verbose=False):
    try:
        from unicorn import Uc, UC_ARCH_M68K, UC_MODE_BIG_ENDIAN, UC_HOOK_CODE, UcError
        from unicorn.m68k_const import (UC_M68K_REG_A7, UC_M68K_REG_D0, UC_M68K_REG_PC,
                                        UC_CPU_M68K_M68020)
    except ImportError:
        print("  (boot self-test skipped: 'pip install unicorn' to enable it)")
        return None
    mag, text, data, bss, nsyms, entry, trs, drs = struct.unpack(">8I", boot_bin[:32])
    BASE = entry or 0xA0000
    # symbol table (a.out nlist, 12 bytes each)
    so = 32 + text + data + trs + drs
    st, strs = boot_bin[so:so + nsyms], boot_bin[so + nsyms:]
    SYM = {}
    for i in range(0, nsyms, 12):
        strx, typ, oth, desc, val = struct.unpack(">IBBHI", st[i:i + 12])
        if typ in (4, 5):
            SYM.setdefault(strs[strx:strs.index(b"\0", strx)].decode("latin1"), val)
    need = ("_sdcmd", "_sd_probe", "_isspinning", "_setpgmap", "_getpgmap", "_setsegmap",
            "_getidprom", "_siopen", "_scopen", "_se_open")
    if any(n not in SYM for n in need):
        print("  (boot self-test skipped: /boot has no usable symbol table)")
        return None
    ROMVEC, STUB, STRS = 0x0FEF0000, 0x0FEF1000, 0x300000
    uc = Uc(UC_ARCH_M68K, UC_MODE_BIG_ENDIAN)
    uc.ctl_set_cpu_model(UC_CPU_M68K_M68020)     # the 3/60 has a 68020
    uc.mem_map(0, 0x1000000)                     # RAM
    uc.mem_map(ROMVEC, 0x10000)                  # fake PROM vector table
    uc.mem_map(0x0FF00000, 0x100000)             # DVMA window (MMU-mapped on real hardware)
    uc.mem_write(BASE, boot_bin[32:32 + text + data])
    uc.mem_write(STRS, devstr.encode() + b"\0")
    uc.mem_write(STRS + 0x100, b"\0")
    uc.mem_write(0x300200, struct.pack(">II", STRS, STRS + 0x100))
    uc.mem_write(0x300300, struct.pack(">I", 0x300200))
    uc.mem_write(ROMVEC + 0x0C, struct.pack(">I", 0x300300))
    uc.mem_write(ROMVEC + 0x38, struct.pack(">I", 0x300400))
    uc.mem_write(ROMVEC + 0x84, struct.pack(">I", STUB))     # v_printf
    uc.mem_write(STUB, b"\x4e\x75")
    disk = open(img_path, "rb")
    rd32 = lambda a: struct.unpack(">I", bytes(uc.mem_read(a, 4)))[0]
    msgs, reads = [], []

    def cstr(a):
        b = b""
        while True:
            c = bytes(uc.mem_read(a, 1))
            if c == b"\0":
                return b.decode("latin1")
            b += c
            a += 1

    def prom_printf():
        sp = uc.reg_read(UC_M68K_REG_A7)
        fmt, args, res, i = cstr(rd32(sp + 4)), sp + 8, "", 0
        while i < len(fmt):
            if fmt[i] != "%":
                res += fmt[i]
                i += 1
                continue
            i += 1
            while fmt[i] in "l-0123456789":
                i += 1
            k = fmt[i]
            i += 1
            v = rd32(args)
            args += 4
            res += (cstr(v) if k == "s" else str(v - (1 << 32) if v & 0x80000000 else v)
                    if k in "dD" else "%x" % v if k in "xX" else chr(v & 255) if k == "c" else "?")
        if msgs and msgs[-1] == res:        # Unicorn re-fires a hook after it touches state
            return
        msgs.append(res)
        print("    [boot] " + res.rstrip("\n"))

    def sdcmd():                                  # READ(6) served from the image file
        sp = uc.reg_read(UC_M68K_REG_A7)
        io = rd32(sp + 8)
        dev = rd32(io + 6)
        sector = rd32(io + 30) + (rd32(dev + 8) if dev else 0)
        buf, cnt = rd32(io + 34), rd32(io + 38)
        disk.seek(sector * SECTOR)
        uc.mem_write(buf, disk.read(cnt).ljust(cnt, b"\0"))
        reads.append(sector)
        uc.reg_write(UC_M68K_REG_D0, cnt)

    def getidprom():
        sp = uc.reg_read(UC_M68K_REG_A7)
        buf, n = rd32(sp + 4), rd32(sp + 8)
        idp = bytearray(32)
        idp[0], idp[1] = 1, 0x17                  # Sun-3/60
        uc.mem_write(buf, bytes(idp[:n] if n else idp))

    ok0 = lambda: uc.reg_write(UC_M68K_REG_D0, 0)
    ok1 = lambda: uc.reg_write(UC_M68K_REG_D0, 1)
    hooks = {SYM["_sdcmd"]: sdcmd, SYM["_sd_probe"]: ok1, SYM["_isspinning"]: ok1,
             SYM["_setpgmap"]: ok0, SYM["_getpgmap"]: ok0, SYM["_setsegmap"]: ok0,
             SYM["_getidprom"]: getidprom, SYM["_siopen"]: ok0, SYM["_scopen"]: ok0,
             SYM["_se_open"]: ok0, STUB: prom_printf}
    for a in hooks:
        if a != STUB:
            uc.mem_write(a, b"\x4e\x75")          # function body -> rts; hook sets D0 first

    def on_code(u, addr, size, ud):
        if addr in hooks:
            hooks[addr]()
    uc.hook_add(UC_HOOK_CODE, on_code, BASE, BASE + text + data + bss + 0x1000)
    uc.hook_add(UC_HOOK_CODE, on_code, STUB, STUB + 4)
    uc.reg_write(UC_M68K_REG_A7, 0x9FFFC)
    try:
        uc.emu_start(BASE + 0x3C, 0, count=6_000_000)     # srt0 "begin"
    except UcError as e:                                  # normal: stops at the kernel entry
        if uc.reg_read(UC_M68K_REG_PC) not in (0x4000, BASE) and verbose:
            print("    emulator stopped at pc=%#x: %s" % (uc.reg_read(UC_M68K_REG_PC), e))
    pc = uc.reg_read(UC_M68K_REG_PC)
    mag2, t2, d2 = struct.unpack(">3I", vmunix_bin[:12])
    loaded = bytes(uc.mem_read(0x4000, t2 + d2)) == vmunix_bin[32:32 + t2 + d2]
    sized = any(m.startswith("Size:") for m in msgs)
    failed = any("boot failed" in m or "not found" in m or "Not " in m for m in msgs)
    good = sized and loaded and not failed
    print("  boot self-test: %s  (%d disk reads; kernel image in RAM %s /vmunix)"
          % ("PASS" if good else "FAIL", len(reads), "matches" if loaded else "DOES NOT match"))
    return good

# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------
ROOT_TARS = ["sun3_root.tar", "sun3_pub.tar"]
USR_TARS = ["sun3_usr.tar", "sun3_sys.tar", "sun3_setup.tar", "sun3_networking.tar",
            "sun3_debugging.tar", "sun3_text.tar", "sun3_system_v.tar", "sun3_manual.tar",
            "sun3_games.tar", "sun3_demo.tar", "sun3_standalone_diags.tar",
            "sun3_fortran.tar", "sun3_user_diag.tar", "sun3_suncore.tar",
            "sun3_pascal.tar", "sun3_profiled_libraries.tar", "sun3_sunview_demo.tar",
            "sun3_sunview_users.tar", "sun3_sunview_programmers.tar", "sun3_uucp.tar",
            "sun3_sunpro.tar", "sun3_versatec.tar"]


class Source:
    """either the .tar.bz2 bundle or an already-extracted directory"""

    def __init__(self, path):
        self.path = path
        self.bundle = None
        if os.path.isdir(path):
            self.dir = path
        else:
            self.bundle = tarfile.open(path, "r:*")
            self.names = {os.path.basename(m.name): m for m in self.bundle if m.isfile()}

    def read(self, name):
        if self.bundle:
            return self.bundle.extractfile(self.names[name]).read()
        with open(os.path.join(self.dir, name), "rb") as f:
            return f.read()

    def tar(self, name):
        return tarfile.open(fileobj=io.BytesIO(self.read(name)), mode="r:", encoding="latin1")


def build(args):
    now = int(time.time())
    src = Source(args.source)
    nhead, nsect = 16, 32
    spc = nhead * nsect
    cyl_mb = spc * SECTOR / (1024.0 * 1024.0)
    root_cyl = int(round(args.root_mb / cyl_mb))
    swap_cyl = int(round(args.swap_mb / cyl_mb))
    usr_cyl = int(round(args.usr_mb / cyl_mb))
    ncyl = root_cyl + swap_cyl + usr_cyl
    acyl = 2
    # The SunOS 3.5 standalone boot program (/boot) keeps the size of the partition it
    # boots from in a 16-bit quantity (sdopen: "andil #0xffff" on dkl_nblk) and then
    # clamps every transfer to that many sectors.  A root partition of 65536 sectors
    # therefore reads as size 0 and nothing can be loaded ("boot failed").  The kernel's
    # own sd driver has no such limit, so only the boot partition (a) is constrained.
    if root_cyl * spc >= 65536:
        raise SystemExit("root partition must be smaller than 65536 sectors (%.1f MiB) so that "
                         "the SunOS 3.5 /boot program can read it; use --root-mb %d or less"
                         % (65536 * SECTOR / 1048576.0, int(65535 // spc * cyl_mb)))
    if (ncyl + acyl) * spc > 2 ** 21:
        print("warning: image is larger than 1 GiB; SunOS 3.5's SCSI driver uses 6-byte "
              "CDBs and cannot address beyond 2^21 sectors", file=sys.stderr)
    total_sectors = (ncyl + acyl) * spc
    img = bytearray(total_sectors * SECTOR)

    # ---- root filesystem tree ----
    rt = Tree(now)
    for t in ROOT_TARS:
        n = rt.add_tar(src.tar(t))
        print("  root  <- %-28s %5d entries" % (t, n))
    add_devices(rt, now)
    hn = args.hostname
    fstab = ("/dev/sd0a / 4.2 rw 1 1\n"
             "/dev/sd0b nodir swap ro 0 0\n"
             "/dev/sd0g /usr 4.2 rw 1 2\n")
    rt.put_file("etc/fstab", fstab)
    rb = rt.lookup("etc/rc.boot")
    rb.data = rb.data.replace(b"hostname=noname", ("hostname=%s" % hn).encode(), 1)
    hosts = rt.lookup("etc/hosts")
    hosts.data = hosts.data + ("%s\t%s\n" % (args.ip, hn)).encode()
    rt.put_file("etc/setup.info", "standalone installation built from the SunOS 3.5 media\n")
    # Standalone machine, no Yellow Pages (NIS).  Do what the installer's `setup` does for
    # "YP: None": rename /etc/ypbind (rc.local only starts it if it exists).  Otherwise
    # ypbind retries forever: "yp: server not responding for domain noname; still trying".
    etc = rt.lookup("etc")
    etc.children["ypbind.orig"] = etc.children.pop("ypbind")
    # the "+:" lines in passwd/group are YP includes; with no YP they are dead weight
    for f in ("etc/passwd", "etc/group"):
        node = rt.lookup(f)
        node.data = b"".join(l for l in node.data.splitlines(True) if l.strip() != b"+:")

    # ---- usr filesystem tree ----
    ut = Tree(now)
    for t in USR_TARS:
        n = ut.add_tar(src.tar(t))
        print("  /usr  <- %-28s %5d entries" % (t, n))

    # ---- lay out and write the filesystems ----
    root_sect = root_cyl * spc
    swap_sect = swap_cyl * spc
    usr_sect = usr_cyl * spc
    root_fs = UFS(img, 0, root_sect, nhead, nsect, mnt="/", now=now)
    root_fs.populate(rt)
    rtot = root_fs.finalize()
    usr_start_cyl = root_cyl + swap_cyl
    usr_fs = UFS(img, usr_start_cyl * spc, usr_sect, nhead, nsect, mnt="/usr", now=now)
    usr_fs.populate(ut)
    utot = usr_fs.finalize()

    # ---- boot block + label ----
    bootsd = ut.lookup("mdec/bootsd").data
    if len(bootsd) > 15 * SECTOR:
        raise ValueError("bootsd too large")
    img[SECTOR:SECTOR + len(bootsd)] = bootsd     # installboot: dd bs=1b count=15 seek=1
    lab = make_label("ZuluSCSI SunOS3.5 cyl %d alt %d hd %d sec %d" % (ncyl, acyl, nhead, nsect),
                     ncyl, acyl, nhead, nsect,
                     {"a": (0, root_sect), "b": (root_cyl, swap_sect),
                      "c": (0, ncyl * spc), "g": (usr_start_cyl, usr_sect)})
    img[0:SECTOR] = lab

    with open(args.output, "wb") as f:
        f.write(img)
    result = None
    if not args.no_verify:
        print("\nrunning the real /boot program against the new image (emulated Sun-3):")
        result = verify_boot(args.output, rt.lookup("boot").data, rt.lookup("vmunix").data)
    print()
    print("image: %s  (%d bytes, %.1f MiB)" % (args.output, len(img), len(img) / 1048576.0))
    print("geometry: %d cyl + %d alt, %d heads, %d sectors/track" % (ncyl, acyl, nhead, nsect))
    for nm, cyl0, cyl, fs, tot in (("a /", 0, root_cyl, root_fs, rtot),
                                   ("g /usr", usr_start_cyl, usr_cyl, usr_fs, utot)):
        print("  sd0%-7s start cyl %4d, %4d cyl (%.0f MiB); %d inodes used, %d KiB free"
              % (nm, cyl0, cyl, cyl * cyl_mb, fs.ncg * fs.ipg - tot[2],
                 (tot[1] * FRAG + tot[3]) * FSIZE // 1024))
    print("  sd0b swap  start cyl %4d, %4d cyl (%.0f MiB)" % (root_cyl, swap_cyl, swap_cyl * cyl_mb))
    print("\nname the file HD0.img on the ZuluSCSI card (SCSI ID 0), then at the PROM: b sd(0,0,0)")
    if result is False:
        sys.exit("boot self-test FAILED -- do not use this image")
    return img


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("source", help="sunos35_tar.bz2, or the extracted sun3_sunos3.5 directory")
    ap.add_argument("output", help="output image file")
    ap.add_argument("--root-mb", type=int, default=31,
                    help="root partition size; must stay under 32 MiB (boot program limit)")
    ap.add_argument("--swap-mb", type=int, default=48)
    ap.add_argument("--usr-mb", type=int, default=256)
    ap.add_argument("--no-verify", action="store_true", help="skip the emulated /boot self-test")
    ap.add_argument("--hostname", default="sun360")
    ap.add_argument("--ip", default="192.9.200.1")
    build(ap.parse_args())
