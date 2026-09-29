-- Prove2me | solution 1 for TropicalLA.tmul_add_distrib
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:17:59.952045+00:00
-- url     : https://prove2.me/submissions/94337be7-1652-4702-9ce2-22514ef056ea

-- Sol generated from Algebra/TropicalLinearAlgebra/TropicalMatrix.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_MaxPlusSemiring
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Theorems.Thm_TropicalLA_le_tmul
import Theorems.Thm_TropicalLA_tmul_le
/-
# Tropical (max-plus) matrices with finite entries

For matrices with entries in `ℝ` (i.e. no `-∞` entries) tropical multiplication is

  `(A ⊗ B) i j = max_k (A i k + B k j)`,

implemented with `Finset.sup'`.  We prove

* `tmul_assoc` : tropical matrix multiplication is associative (a hands-on proof,
  independent of the semiring instance);
* `tmul_embed`  : this operation agrees with multiplication in `Matrix ι ι (MaxPlus ℝ)`,
  so the two developments are coherent;
* `tpow_isGreatest` : **max-plus powers compute optimal paths** — the `(i,j)` entry of
  `A^{⊗(m+1)}` is the maximal weight of a length-`(m+1)` walk from `i` to `j`
  (the algebraic form of the Bellman dynamic-programming principle).
-/

open TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]





















open TropicalLA in
theorem solution(A B C : Matrix ι ι ℝ) (i j : ι) :
    tmul A (fun i j => max (B i j) (C i j)) i j = max (tmul A B i j) (tmul A C i j) := by
  apply le_antisymm
  · refine tmul_le fun k => ?_
    show A i k + max (B k j) (C k j) ≤ _
    rcases le_total (B k j) (C k j) with h | h
    · rw [max_eq_right h]
      exact le_trans (le_tmul A C i j k) (le_max_right _ _)
    · rw [max_eq_left h]
      exact le_trans (le_tmul A B i j k) (le_max_left _ _)
  · refine max_le (tmul_le fun k => ?_) (tmul_le fun k => ?_)
    · have h1 := le_tmul A (fun i j => max (B i j) (C i j)) i j k
      have h2 := le_max_left (B k j) (C k j)
      simp only at h1
      linarith
    · have h1 := le_tmul A (fun i j => max (B i j) (C i j)) i j k
      have h2 := le_max_right (B k j) (C k j)
      simp only at h1
      linarith
