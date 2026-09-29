-- Prove2me | Theorems.Thm_TropicalLA_tpow_isGreatest
-- name    : TropicalLA.tpow_isGreatest
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:59:52.243967+00:00
-- url     : https://prove2.me/theorems/2bb9b793-dc46-4bc1-a567-53394e044868
-- title:
--   Tropical powers compute maximum-weight walks.
-- statement:
--   **Tropical powers compute maximum-weight walks.**  The `(i,j)` entry of the
--   `(m+1)`-st tropical power of `A` is the greatest weight of a walk of length `m+1`
--   from `i` to `j`; in particular that optimum is attained.
--
--   ```lean
--   theorem TropicalLA.tpow_isGreatest(A : Matrix ι ι ℝ) (m : ℕ) (i j : ι) :
--       IsGreatest {w : ℝ | ∃ p : ℕ → ι, p 0 = i ∧ p (m + 1) = j ∧ w = pathWeight A p (m + 1)}
--         (tpow A m i j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalMatrix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalMatrix.lean#L124

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

theorem TropicalLA.tpow_isGreatest(A : Matrix ι ι ℝ) (m : ℕ) (i j : ι) :
    IsGreatest {w : ℝ | ∃ p : ℕ → ι, p 0 = i ∧ p (m + 1) = j ∧ w = pathWeight A p (m + 1)}
      (tpow A m i j) := by sorry
