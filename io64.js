// framebender driver effects: native builds only (bend main.bend -o framebender).
io_eff(CID(Io.write_fd), (fd, data) => io_fail(38));
io_eff(CID(Io.read_block), (file, max, gz) => io_tup(file, io_fail(38)));
io_eff(CID(Io.fa_read), (file, hi, lo, shi, slo, chi, clo, bhi, blo, whi, wlo, want) => io_tup(file, io_fail(38)));
io_eff(CID(Io.write_block), (fd, n, a) => 5);
