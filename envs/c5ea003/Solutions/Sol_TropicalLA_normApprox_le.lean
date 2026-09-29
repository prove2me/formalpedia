-- Prove2me | solution 1 for TropicalLA.normApprox_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T22:47:06.179485+00:00
-- url     : https://prove2.me/submissions/42844d74-b0c9-4210-ac97-1e68110d52be

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalReducible
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι (WithBot ℝ)} {lam : ℝ}
    (i j : ι) : normApprox A lam i j ≤ spreadAbs A lam := by
  have hmin := abs_nonneg (entryMin A)
  have hmax := abs_nonneg (entryMax A)
  have hlam := abs_nonneg lam
  have hsp : 1 ≤ spreadAbs A lam := by unfold spreadAbs; linarith
  unfold normApprox
  split_ifs with h
  · -- a `⊥` entry is replaced by the (negative) penalty
    unfold penaltyN
    have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    nlinarith
  · -- a finite entry is at most the largest entry
    have h1 : finPart A i j ≤ entryMax A :=
      Finset.le_sup' (fun p : ι × ι => finPart A p.1 p.2) (Finset.mem_univ (i, j))
    have h2 := le_abs_self (entryMax A)
    have h3 := neg_le_abs lam
    unfold spreadAbs
    linarith
