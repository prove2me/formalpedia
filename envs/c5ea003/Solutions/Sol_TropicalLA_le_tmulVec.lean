-- Prove2me | solution 1 for TropicalLA.le_tmulVec
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:13:07.329192+00:00
-- url     : https://prove2.me/submissions/dd0f4b58-db87-4e11-bf0b-f0742f04112f

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
theorem solution(A : Matrix ι ι ℝ) (v : ι → ℝ) (i j : ι) : A i j + v j ≤ tmulVec A v i :=
  Finset.le_sup' (fun j => A i j + v j) (Finset.mem_univ j)
