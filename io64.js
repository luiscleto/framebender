// framebender driver effects: native builds only (bend main.bend -o framebender).
io_eff(CID(Io.pread_full), (file, hi, lo, n) => io_tup(file, io_fail(38)));
io_eff(CID(Io.write_fd), (fd, data) => io_fail(38));
