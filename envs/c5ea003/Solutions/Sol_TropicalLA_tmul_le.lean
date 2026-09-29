-- Prove2me | solution 1 for TropicalLA.tmul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:15:40.716712+00:00
-- url     : https://prove2.me/submissions/aee6c9ef-9ad8-499e-8ec3-3826c6779f01

-- Sol generated from Algebra/TropicalLinearAlgebra/TropicalMatrix.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_MaxPlusSemiring
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
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
theorem solution{A B : Matrix ι ι ℝ} {i j : ι} {c : ℝ} (h : ∀ k, A i k + B k j ≤ c) :
    tmul A B i j ≤ c := Finset.sup'_le _ _ fun k _ => h k
