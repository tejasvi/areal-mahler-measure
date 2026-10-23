import ArealUCore.Check

/-! Segmented node pass for the upper K chord shards. `chordFin` is `chordLB` with the node-pass result `r` as a
parameter (`chordLB_eq_fin`, by unfolding), and `leafPass` is a fold, so a chord check splits into kernel-checked folds over
four segments of the node records with literal intermediate accumulators (`chordOK_of_segs`): each `decide +kernel` then
evaluates a quarter of the records, which keeps the kernel's time and memory per check low. `leavesOK_two` assembles a
two-leaf shard from its leaf checks. Every claim is proved generically; the shards only instantiate these lemmas. -/

namespace ArealUCore

deriving instance DecidableEq for LAcc

/-- `chordLB` with the node-pass result `r` given. -/
def chordFin (c : Ctx) (Xp Xq k : Nat) (x0q : Bool) (mask : Nat) (r : LAcc) : Option (Int × Int) :=
  let D : Nat := DEC * 2 ^ k
  let H : Nat := Xq - Xp
  if Xp < Xq ∧ ¬ (Xp < D ∧ D < Xq) ∧ H ≤ D then
    let LD := logT c.tab c.l2 D 1
    if r.inside then none else
    let base : Int := c.isLo - c.m0hi
    let polyRes := (List.zip polys (List.zip cwNum cwSh)).zipIdx.foldl
      (fun (acc : Option (Int × Int × Int × Int × Int)) (x : (List Int × Nat × Nat) × Nat) =>
        match acc with
        | none => none
        | some (ap, aq, t0, sl, mp) =>
          match polyLeaf c.tab c.l2 Xp Xq D LD x0q (Nat.testBit mask x.2) x.1.1 x.1.2.1 x.1.2.2 with
          | none => none
          | some (ap', aq', t0', sl', mp') => some (ap + ap', aq + aq', t0 + t0', sl + sl', mp + mp'))
      (some (0, 0, 0, 0, 0))
    match polyRes with
    | none => none
    | some (pap, paq, t0, sl, mp) =>
      let Ap := base + pap - 2 * uHi (r.spl, r.sph) D
      let Aq := base + paq - 2 * uHi (r.sql, r.sqh) D
      let mn : Int := if 0 < r.m then cdiv (r.m * (H : Int) * (H : Int)) (D * D * 2 ^ QS) else 0
      let corr : Int := cdiv (mn + mp) 8
      if x0q then some (Ap + t0 + sl - corr, Aq + t0 - corr)
      else some (Ap + t0 - corr, Aq + t0 + sl - corr)
  else none

theorem chordLB_eq_fin (c : Ctx) (Xp Xq k : Nat) (x0q : Bool) (mask : Nat) :
    chordLB c Xp Xq k x0q mask =
      chordFin c Xp Xq k x0q mask (leafPass c.tab c.l2 c.rs k Xp Xq (logT c.tab c.l2 (DEC * 2 ^ k) 1)) := by
  unfold chordLB chordFin
  rfl

theorem leafPass_split (tab : Nat) (l2 : Nat × Nat) (rs : List NRec) (k Xp Xq : Nat) (LD : Int × Int) (n : Nat) :
    leafPass tab l2 rs k Xp Xq LD =
      (rs.drop n).foldl (leafStep tab l2 k Xp Xq LD) ((rs.take n).foldl (leafStep tab l2 k Xp Xq LD) ⟨0, 0, 0, 0, 0, false⟩) := by
  unfold leafPass
  rw [← List.foldl_append, List.take_append_drop]

theorem foldl_split {α β : Type} (f : α → β → α) (a : α) (l : List β) (n : Nat) :
    l.foldl f a = (l.drop n).foldl f ((l.take n).foldl f a) := by
  rw [← List.foldl_append, List.take_append_drop]

end ArealUCore

namespace ArealUCore

/-- The verdict of `chordOK` from a given node-pass result. -/
def chordFinOK (c : Ctx) (Xp Xq k : Nat) (x0q : Bool) (mask : Nat) (r : LAcc) : Bool :=
  match chordFin c Xp Xq k x0q mask r with
  | some (lp, lq) => decide (0 < lp) && decide (0 < lq)
  | none => false

theorem chordOK_eq_finOK (c : Ctx) (Xp Xq k : Nat) (x0q : Bool) (mask : Nat) :
    chordOK c Xp Xq k x0q mask =
      chordFinOK c Xp Xq k x0q mask (leafPass c.tab c.l2 c.rs k Xp Xq (logT c.tab c.l2 (DEC * 2 ^ k) 1)) := by
  unfold chordOK chordFinOK
  rw [chordLB_eq_fin]
  rfl

/-- A chord check from the four segment folds of its node pass and the remainder `chordFin`. -/
theorem chordOK_of_segs (c : Ctx) (Xp Xq k : Nat) (x0q : Bool) (mask S : Nat) (A1 A2 A3 A4 : LAcc)
    (h1 : (c.rs.take S).foldl (leafStep c.tab c.l2 k Xp Xq (logT c.tab c.l2 (DEC * 2 ^ k) 1)) ⟨0, 0, 0, 0, 0, false⟩ = A1)
    (h2 : ((c.rs.drop S).take S).foldl (leafStep c.tab c.l2 k Xp Xq (logT c.tab c.l2 (DEC * 2 ^ k) 1)) A1 = A2)
    (h3 : (((c.rs.drop S).drop S).take S).foldl (leafStep c.tab c.l2 k Xp Xq (logT c.tab c.l2 (DEC * 2 ^ k) 1)) A2 = A3)
    (h4 : (((c.rs.drop S).drop S).drop S).foldl (leafStep c.tab c.l2 k Xp Xq (logT c.tab c.l2 (DEC * 2 ^ k) 1)) A3 = A4)
    (hf : chordFinOK c Xp Xq k x0q mask A4 = true) :
    chordOK c Xp Xq k x0q mask = true := by
  rw [chordOK_eq_finOK, leafPass_split _ _ _ _ _ _ _ S, h1, foldl_split _ _ _ S, h2, foldl_split _ _ _ S, h3, h4]
  exact hf

theorem leafOK_chord (c : Ctx) (X1 X2 k : Nat) (x0q : Bool) (mask : Nat)
    (h : chordOK c X1 X2 k x0q mask = true) : leafOK c ⟨0, X1, X2, k, x0q, mask⟩ = true := by
  simpa [leafOK] using h

theorem leafOK_window (c : Ctx) (X1 X2 k : Nat) (x0q : Bool) (mask : Nat)
    (h : windowOK c X1 X2 k = true) : leafOK c ⟨1, X1, X2, k, x0q, mask⟩ = true := by
  simpa [leafOK] using h

/-- Two consecutive leaves. -/
theorem leavesOK_two (c : Ctx) (X kx XT kT : Nat) (l1 l2 : Leaf)
    (h0 : ptEq X kx l1.X1 l1.k = true) (h1 : leafOK c l1 = true) (h01 : ptEq l1.X2 l1.k l2.X1 l2.k = true)
    (h2 : leafOK c l2 = true) (h3 : ptEq l2.X2 l2.k XT kT = true) :
    leavesOK c X kx [l1, l2] XT kT = true := by
  simp [leavesOK, h0, h1, h01, h2, h3]

end ArealUCore
