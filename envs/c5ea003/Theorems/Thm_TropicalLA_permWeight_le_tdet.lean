-- Prove2me | Theorems.Thm_TropicalLA_permWeight_le_tdet
-- name    : TropicalLA.permWeight_le_tdet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:59:13.524999+00:00
-- url     : https://prove2.me/theorems/9a028efd-b199-4eb7-b19b-875e25634478
-- title:
--   PermWeight le tdet
-- statement:
--   Formal statement of `TropicalLA.permWeight_le_tdet` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalLA.permWeight_le_tdet(A : Matrix ι ι ℝ) (σ : Equiv.Perm ι) : permWeight A σ ≤ tdet A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalDeterminant.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalDeterminant.lean#L34

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

theorem TropicalLA.permWeight_le_tdet(A : Matrix ι ι ℝ) (σ : Equiv.Perm ι) : permWeight A σ ≤ tdet A := by sorry
