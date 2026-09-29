-- Prove2me | Theorems.Thm_TropicalLA_exists_tmulVec_eq
-- name    : TropicalLA.exists_tmulVec_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:59:20.943039+00:00
-- url     : https://prove2.me/theorems/8dccfda0-ffa1-4b49-8434-e59730d5585f
-- title:
--   Exists tmulVec eq
-- statement:
--   Formal statement of `TropicalLA.exists_tmulVec_eq` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalLA.exists_tmulVec_eq(A : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι) :
--       ∃ j, tmulVec A v i = A i j + v j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalMatrix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalMatrix.lean#L46

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

theorem TropicalLA.exists_tmulVec_eq(A : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι) :
    ∃ j, tmulVec A v i = A i j + v j := by sorry
