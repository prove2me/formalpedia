-- Prove2me | solution 1 for TropicalLA.tmul_assoc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:17:57.741011+00:00
-- url     : https://prove2.me/submissions/69284378-50cc-41a4-afb6-488f81a96810

-- Sol generated from Algebra/TropicalLinearAlgebra/TropicalMatrix.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_MaxPlusSemiring
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Theorems.Thm_TropicalLA_exists_tmul_eq
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
theorem solution(A B C : Matrix ι ι ℝ) : tmul (tmul A B) C = tmul A (tmul B C) := by
  funext i j
  apply le_antisymm
  · refine tmul_le fun k => ?_
    obtain ⟨l, hl⟩ := exists_tmul_eq A B i k
    have h1 := le_tmul B C l j k
    have h2 := le_tmul A (tmul B C) i j l
    rw [hl]; linarith
  · refine tmul_le fun l => ?_
    obtain ⟨k, hk⟩ := exists_tmul_eq B C l j
    have h1 := le_tmul A B i k l
    have h2 := le_tmul (tmul A B) C i j k
    rw [hk]; linarith
