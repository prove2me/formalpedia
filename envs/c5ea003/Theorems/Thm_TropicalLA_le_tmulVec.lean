-- Prove2me | Theorems.Thm_TropicalLA_le_tmulVec
-- name    : TropicalLA.le_tmulVec
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:59:12.048688+00:00
-- url     : https://prove2.me/theorems/e4082c6c-2428-46aa-b985-5c3cd72805ef
-- title:
--   Le tmulVec
-- statement:
--   Formal statement of `TropicalLA.le_tmulVec` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalLA.le_tmulVec(A : Matrix ι ι ℝ) (v : ι → ℝ) (i j : ι) : A i j + v j ≤ tmulVec A v i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalMatrix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalMatrix.lean#L43

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalMatrix.lean
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

theorem TropicalLA.le_tmulVec(A : Matrix ι ι ℝ) (v : ι → ℝ) (i j : ι) : A i j + v j ≤ tmulVec A v i := by sorry
