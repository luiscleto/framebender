import Base
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as B
import lawful-bytes@0.1.1.0/fast.bend as F
import lawful-bytes@0.1.1.0/LAWS.bend as L
import lawful-bytes@0.1.1.0/PROOF.bend as LP

# fast.bend's operations give bytes.bend's results: lawful-bytes' fast laws
# (LAWS.bend, proven in PROOF.bend), restated where the phase-B proofs reach
# fast.bend. The searches equal the reference only on a well-formed buffer,
# for a range within it and a byte value; the pair forms (the same Bytes
# handed back) hold for any arguments.

def find_pair(b: D.Bytes, +from: U32, +to: U32, +c: U32) ->
  {F.find(b, from, to, c) == (b, Pair.snd(D.Bytes, U32, F.find(b, from, to, c))) : D.Bytes & U32}:
  L.fast_find_pair(b, from, to, c)

def find2_pair(b: D.Bytes, +from: U32, +to: U32, +c1: U32, +c2: U32) ->
  {F.find2(b, from, to, c1, c2) == (b, Pair.snd(D.Bytes, U32, F.find2(b, from, to, c1, c2))) : D.Bytes & U32}:
  L.fast_find2_pair(b, from, to, c1, c2)

def find_eq(b: D.Bytes, +d: Nat, +from: U32, +to: U32, +c: U32,
  h: {D.ok(b, d) == True{} : Bool},
  hft: {U32.is_le(from, to) == True{} : Bool},
  ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool},
  hc: {U32.is_lt(c, 256) == True{} : Bool}) ->
  {F.find(b, from, to, c) == B.find(b, from, to, c) : D.Bytes & U32}:
  L.fast_find(b, d, from, to, c, h, hft, ht, hc)

def find2_eq(b: D.Bytes, +d: Nat, +from: U32, +to: U32, +c1: U32, +c2: U32,
  h: {D.ok(b, d) == True{} : Bool},
  hft: {U32.is_le(from, to) == True{} : Bool},
  ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool},
  hc1: {U32.is_lt(c1, 256) == True{} : Bool},
  hc2: {U32.is_lt(c2, 256) == True{} : Bool}) ->
  {F.find2(b, from, to, c1, c2) == B.find2(b, from, to, c1, c2) : D.Bytes & U32}:
  L.fast_find2(b, d, from, to, c1, c2, h, hft, ht, hc1, hc2)

# append is not equal to bytes.bend's as a value (it may write up to 3 bytes
# past the new length, which view does not read); it satisfies the same laws.
def append_view(dst: D.Bytes, src: D.Bytes, +d: Nat, +e: Nat, +s: U32, +n: U32,
  hd: {D.ok(dst, d) == True{} : Bool}, he: {D.ok(src, e) == True{} : Bool},
  hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(n)), D.size(src)) == True{} : Bool},
  hc: {Nat.is_le(Nat.add(D.size(dst), U32.to_nat(n)), D.cap(dst)) == True{} : Bool}) ->
  {D.view(Pair.fst(D.Bytes, D.Bytes, F.append(dst, src, s, n))) == List.append(&2, U32, D.view(dst), D.slice(D.view(src), U32.to_nat(s), U32.to_nat(n))) : List<&2, U32>}:
  L.fast_append_view(dst, src, d, e, s, n, hd, he, hs, hc)

def append_ok(dst: D.Bytes, src: D.Bytes, +d: Nat, +s: U32, +n: U32,
  hd: {D.ok(dst, d) == True{} : Bool},
  hc: {Nat.is_le(Nat.add(D.size(dst), U32.to_nat(n)), D.cap(dst)) == True{} : Bool}) ->
  {D.ok(Pair.fst(D.Bytes, D.Bytes, F.append(dst, src, s, n)), d) == True{} : Bool}:
  L.fast_append_ok(dst, src, d, s, n, hd, hc)

def append_pair(dst: D.Bytes, src: D.Bytes, +s: U32, +n: U32) ->
  {F.append(dst, src, s, n) == (Pair.fst(D.Bytes, D.Bytes, F.append(dst, src, s, n)), src) : D.Bytes & D.Bytes}:
  L.fast_append_pair(dst, src, s, n)
