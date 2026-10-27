import Base
import ./types.bend as B
import ./protocol.bend as P

# Stub of the implementation interface, only so that the draft type-checks.

type St is Data:
  St{o: B.Opts}

type Step is Data:
  Step{st: St, out: String, notes: List<&2, B.Note>, next: P.Next}

type Begin is Data:
  Begin{st: St, ref: String, vcf: String}
  Usage{}

def start(argv: List<&2, String>) -> Begin:
  Usage{}

def step(st: St, i: P.In) -> Step:
  Step{st, "", Nil{}, P.Finish{1n}}
