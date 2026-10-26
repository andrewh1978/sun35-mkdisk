# What

This script will build a disk image that can be dropped onto a ZuluSCSI device, or presumably a real disk, and used to boot SunOS 3.5. It has been tested on a Sun 3/60 workstation.

# Why

I have an old Sun 3/60 that came with no storage. The ZuluSCSI firmware appears to have a [bug](https://github.com/ZuluSCSI/ZuluSCSI-firmware/issues/1005) that prevents booting from tape.

# How

Download and unpack the [tape images](https://fsck.technology/software/Sun%20Microsystems/SunOS%20Install%20Media/SunOS%203.5%20Sun-3%20%28Tape%29/).

```
python3 mkdisk.py /path/to/tape/tars sunos35.img [ --swap-mb N ] [ --usr-mb N ] [ --hostname NAME ] [ --ip IP ]
```

# Disclaimer

Claude wrote this in its entirety.
