-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR7_exp_one_mul_log_le_rpow_div
-- name    : ErdosProblems.Erdos257.PaperCompleteR7.exp_one_mul_log_le_rpow_div
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:04:31.483971+00:00
-- url     : https://prove2.me/theorems/789e6ce0-2008-4956-b35c-618f017b35dd
-- title:
--   Logarithm bound by a fractional power
-- statement:
--   For t≥1 and 0<α≤1, e·log t is at most t^α/(2^α−1).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR7/CoverKernel.lean#L186-L211
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Finite and scalar kernel of the strengthened positive cover

The short note's `thm:variable-fractional-cover` and `res:mixed-supports` are
not available as end-to-end Lean theorems. Their proofs use three ingredients
that are finite or scalar, and those are isolated here as ordinary theorems.

* `rpow_sum_le_sum_rpow` and `rpow_tsum_le_tsum_rpow` are the subadditivity of a
  fractional power used to pass from the dyadic observation mean `U_j(N)` to the
  divisor majorant `V_j(N)`.
* `rpow_neg_le_max_one_inv` is the scalar step `ε ^ (-α) ≤ max 1 ε⁻¹` that makes
  the tail budget choice uniform over the exponents `α_j`.
* `tsum_inv_pow_succ` and `tsum_rpow_two_inv_succ` evaluate the geometric factor
  `1 / (2 ^ α - 1)` appearing in the displayed cost condition (V).

Round 7 wave 2 adds the finite and scalar steps that the same two proofs use
further down: the complete-orbit facts of the observation kernel `w_{B,d}`
(`mul_sub_one_le_pow_sub_one`, `cycle_ratio_le_inv_sub_one`,
`sum_cycle_weight_eq`), the scalar minimisation behind the cover-cost display
(`two_rpow_sub_one_le_self`, `exp_one_mul_le_exp`,
`exp_one_mul_log_le_rpow_div`, which is the second inequality of the note's
cover-log obstruction for every admissible exponent), and the atom inequality
`(b^r-1)/(b^d-1) <= 2 (2^r-1)/(2^d-1)` that carries the base-two conclusion to
every integer base (`atom_base_transfer`), the one-sample step of the averaged
tail test (`exists_lt_of_mean_lt`), and the geometric lower bound of the no-wrap
case (`two_mul_sqrt_mul_le_add`, `card_mul_sqrt_le_geom_sum`).

None of these is the analytic theorem. The irrationality conclusion still needs
the one sampling step that is neither finite nor scalar: a single `N` at which
the averaged tail test `S_J(N) < 1` holds, obtained from the finite estimate (S)
by averaging over the dyadic ranges. The remaining goal is stated as
`StrengthenedPositiveCoverClaim` in `AnalyticTargets.lean`.
-/

noncomputable section


open Finset Filter











/-! ### Cycle weights of the finite observation kernel

The kernel weight of the short note's estimate (S) is `w_{B,d}(n) = B^(n % d) / (B^d - 1)`.
The two lemmas below are its complete-orbit facts: one full residue cycle carries total
weight exactly `1 / (B - 1)`, and the orbit of a common divisor `g` carries at most the
same total. Both are finite identities in `B`, uniform in `d` as `B` decreases to one. -/







/-! ### The scalar minimisation behind the cover cost

`Ψ(t) = inf_{0 < α ≤ 1} t ^ α / (2 ^ α - 1)` is the cover-independent cost of the short
note's display (eq:cover-log-obstruction). The bound `Ψ(t) ≥ e log t` is proved here for
every admissible exponent, which is the second inequality of that display. The first
inequality, the averaging over `F` against the uniform mean modulo `lcm F`, is not here. -/

open ErdosProblems.Erdos257.PaperCompleteR7

theorem ErdosProblems.Erdos257.PaperCompleteR7.exp_one_mul_log_le_rpow_div {t α : ℝ} (ht : 1 ≤ t) (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.exp 1 * Real.log t ≤ t ^ α / ((2 : ℝ) ^ α - 1) := by sorry
end
