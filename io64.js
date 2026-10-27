// framebender driver effects: native builds only (bend main.bend -o framebender).
io_eff(CID(Io.write_fd), (fd, data) => io_fail(38));
io_eff(CID(Io.read_block), (file, max) => io_tup(file, io_fail(38)));
io_eff(CID(Io.fa_read), (file, hi, lo, shi, slo, col, lb, lw, want) => io_tup(file, io_fail(38)));
io_eff(CID(Io.write_block), (fd, n, a) => 5);
