import Base

def f(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == (a && b && c) : Bool}:
  {==}
