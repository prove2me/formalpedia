-- Prove2me | solution 1 for TropicalLA.permWeight_le_tdet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:13:06.609551+00:00
-- url     : https://prove2.me/submissions/22280c19-d5b8-4343-b140-837914f5378d

-- Sol generated from Algebra/TropicalLinearAlgebra/TropicalDeterminant.lean
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











open TropicalLA in
theorem solution(A : Matrix ι ι ℝ) (σ : Equiv.Perm ι) : permWeight A σ ≤ tdet A :=
  Finset.le_sup' (permWeight A) (Finset.mem_univ σ)
