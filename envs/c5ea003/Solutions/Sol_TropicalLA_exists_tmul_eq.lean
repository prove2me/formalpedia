-- Prove2me | solution 1 for TropicalLA.exists_tmul_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:13:08.373268+00:00
-- url     : https://prove2.me/submissions/586c1e1a-7abd-45ba-b85e-6dc103dc841a

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
theorem solution(A B : Matrix ι ι ℝ) (i j : ι) : ∃ k, tmul A B i j = A i k + B k j := by
  obtain ⟨k, _, hk⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) (fun k => A i k + B k j)
  exact ⟨k, hk⟩
