import Base
import ./types.bend as B
import ./norm_seq.bend as Norm

# The machine's step of the header definitions (Norm.defs.line, its prefix
# matched first, so a line is parsed only when it is a definition) is
# B.Defs.line.

def fmt_eq(fmt: Bool, +d: B.Defs, +body: String) ->
  {Norm.defs.fmt(fmt, d, body) == Bool.pick(B.Defs, fmt, B.Defs.add_fmt(B.Hdr.tag(String.drop(body, 10n)), d), d) : B.Defs}:
  match fmt:
    case True{}:
      {==}
    case False{}:
      {==}

def info_eq(info: Bool, +d: B.Defs, +body: String) ->
  {Norm.defs.info(info, d, body) == Bool.pick(B.Defs, info, B.Defs.add_info(B.Hdr.tag(String.drop(body, 8n)), d),
    Bool.pick(B.Defs, String.starts_with(body, "##FORMAT=<"), B.Defs.add_fmt(B.Hdr.tag(String.drop(body, 10n)), d), d)) : B.Defs}:
  match info:
    case True{}:
      {==}
    case False{}:
      fmt_eq(String.starts_with(body, "##FORMAT=<"), d, body)

def line_eq(+d: B.Defs, +body: String) -> {Norm.defs.line(d, body) == B.Defs.line(d, body) : B.Defs}:
  info_eq(String.starts_with(body, "##INFO=<"), d, body)
