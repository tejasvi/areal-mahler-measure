import ArealUCore.Leaves
import ArealUCore.Lits
open ArealUCore

def litI (x : Int) : String := if x < 0 then s!"({x})" else s!"{x}"

def accLit (a : LAcc) : String :=
  s!"⟨{litI a.spl}, {litI a.sph}, {litI a.sql}, {litI a.sqh}, {litI a.m}, {a.inside}⟩"

/-- Native helper for the split upper K shards: `arlseg S LO HI` prints, for each leaf `LO ≤ i < HI`, its fields and (chord
leaves) the accumulators of the node pass after each of the four segments of `ctxLitU.rs` (length `S`, `S`, `S`, rest).
Untrusted hints: every value is re-checked by the kernel in the shard. -/
def main (args : List String) : IO Unit := do
  match args with
  | [sS, sLo, sHi] =>
    let S := sS.toNat!
    let lo := sLo.toNat!
    let hi := sHi.toNat!
    let c := ctxLitU
    let r1 := c.rs.take S
    let r2 := (c.rs.drop S).take S
    let r3 := ((c.rs.drop S).drop S).take S
    let r4 := ((c.rs.drop S).drop S).drop S
    let mut i := lo
    for l in (leaves.drop lo).take (hi - lo) do
      if l.kind = 0 then
        let f := leafStep c.tab c.l2 l.k l.X1 l.X2 (logT c.tab c.l2 (DEC * 2 ^ l.k) 1)
        let a1 := r1.foldl f ⟨0, 0, 0, 0, 0, false⟩
        let a2 := r2.foldl f a1
        let a3 := r3.foldl f a2
        let a4 := r4.foldl f a3
        IO.println s!"{i}\t{l.kind}\t{l.X1}\t{l.X2}\t{l.k}\t{l.x0q}\t{l.mask}\t{accLit a1}\t{accLit a2}\t{accLit a3}\t{accLit a4}"
      else
        IO.println s!"{i}\t{l.kind}\t{l.X1}\t{l.X2}\t{l.k}\t{l.x0q}\t{l.mask}"
      i := i + 1
  | _ => IO.println "usage: arlseg S LO HI"
