-- Prove2me | Theorems.Thm_TropicalLA_exists_permWeight_eq_tdet
-- name    : TropicalLA.exists_permWeight_eq_tdet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:59:41.256522+00:00
-- url     : https://prove2.me/theorems/b1eebab5-3f2b-4f14-8246-c684a3f45f21
-- title:
--   Exists permWeight eq tdet
-- statement:
--   Formal statement of `TropicalLA.exists_permWeight_eq_tdet` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalLA.exists_permWeight_eq_tdet(A : Matrix ι ι ℝ) : ∃ σ, tdet A = permWeight A σ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalDeterminant.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalDeterminant.lean#L37

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalDeterminant.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
/-
# The tropical determinant

Over the max-plus semiring the determinant of `A` (there being no signs) is

  `tdet A = max_{σ ∈ S_ι} Σ_i A i (σ i)`,

i.e. the value of the **optimal assignment problem** for the weight matrix `A`.

Main results:

* `tdet_isGreatest` : the tropical determinant *is* the weight of a maximum-weight
  permutation, and that maximum is attained;
* `tdet_transpose`  : invariance under transposition;
* `tdet_tmul_ge`    : **supermultiplicativity** `tdet A + tdet B ≤ tdet (A ⊗ B)`
  (the tropical Cauchy–Binet inequality); equality can fail — see
  `TropicalLA.Examples.tdet_tmul_strict` in `Examples.lean`;
* `tdet_diag_le` and `tdet_eq_trace_of_diagonally_dominant` : the diagonal always
  gives a lower bound, with equality under a Monge-type dominance condition.
-/

open TropicalLA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem TropicalLA.exists_permWeight_eq_tdet(A : Matrix ι ι ℝ) : ∃ σ, tdet A = permWeight A σ := by sorry
