-- Prove2me | Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
-- name    : Algebra_TropicalLinearAlgebra_TropicalDeterminant
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:18:20.462099+00:00
-- url     : https://prove2.me/theorems/03030436-2b5f-4ec5-a84c-15851da53dcd
-- title:
--   Aether Catalog definitions — Algebra_TropicalLinearAlgebra_TropicalDeterminant
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalLinearAlgebra.TropicalDeterminant`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalLinearAlgebra/TropicalDeterminant.lean by skeleton subtraction
import Mathlib
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

namespace TropicalLA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight of the permutation `σ` in the matrix `A`. -/
def permWeight (A : Matrix ι ι ℝ) (σ : Equiv.Perm ι) : ℝ := ∑ i, A i (σ i)

/-- The **tropical determinant**: the maximal weight of a permutation. -/
noncomputable def tdet (A : Matrix ι ι ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (permWeight A)








end TropicalLA


