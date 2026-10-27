import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_var.bend as PV
import ./proof_window.bend as PW
import ./proof_run.bend as PR
import ./proof_machine.bend as PM

# Proofs of the laws in LAWS.bend: `def L.name` proves `law name`.
# Rewrites: `%e : G` with e : {new == old}; G is the goal with `_` where old
# is; what follows proves G with new there.

# A command line Args.parse rejects starts with a usage error.
def L.usage(argv, ha):
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), None{}, ha) : {Norm.start.of(_) == Norm.Usage{} : Norm.Begin}
  {==}

# Forwarded to the proof files (a law is forwarded once its proof there is
# complete; an open law cannot be called).
