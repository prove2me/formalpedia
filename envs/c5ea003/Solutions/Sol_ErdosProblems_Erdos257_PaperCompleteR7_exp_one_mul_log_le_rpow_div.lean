-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR7.exp_one_mul_log_le_rpow_div
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:09:20.596399+00:00
-- url     : https://prove2.me/submissions/e7d4849b-dc58-459a-ae7f-993fd62d899d

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

namespace ErdosProblems.Erdos257.PaperCompleteR7
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

/-- Convexity of `2 ^ ·` on the unit interval, the exact step the note cites. -/
theorem two_rpow_sub_one_le_self {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (2 : ℝ) ^ α - 1 ≤ α := by
  have h := rpow_one_add_le_one_add_mul_self (s := (1 : ℝ)) (by norm_num) hα0 hα1
  norm_num at h
  linarith

/-- `e u ≤ exp u`, the scalar form of `e ^ u / u ≥ e`. -/
theorem exp_one_mul_le_exp {u : ℝ} (_hu : 0 < u) :
    Real.exp 1 * u ≤ Real.exp u := by
  have h := Real.add_one_le_exp (u - 1)
  have hle : u ≤ Real.exp (u - 1) := by linarith
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  calc Real.exp 1 * u ≤ Real.exp 1 * Real.exp (u - 1) := by
        exact mul_le_mul_of_nonneg_left hle hpos.le
    _ = Real.exp u := by rw [← Real.exp_add]; ring_nf
end ErdosProblems.Erdos257.PaperCompleteR7

open Finset Filter
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR7 in
theorem solution {t α : ℝ} (ht : 1 ≤ t) (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.exp 1 * Real.log t ≤ t ^ α / ((2 : ℝ) ^ α - 1) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have h2 : (1 : ℝ) < (2 : ℝ) ^ α :=
    Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, hα⟩)
  have hden : (0 : ℝ) < (2 : ℝ) ^ α - 1 := by linarith
  have htpos : (0 : ℝ) < t ^ α := Real.rpow_pos_of_pos ht0 α
  have hstep : t ^ α / α ≤ t ^ α / ((2 : ℝ) ^ α - 1) :=
    div_le_div_of_nonneg_left htpos.le hden (two_rpow_sub_one_le_self hα.le hα1)
  refine le_trans ?_ hstep
  rcases eq_or_lt_of_le hlog with hz | hz
  · rw [← hz]
    simp only [mul_zero]
    positivity
  · have hu : 0 < α * Real.log t := mul_pos hα hz
    have hexp : t ^ α = Real.exp (α * Real.log t) := by
      rw [Real.rpow_def_of_pos ht0]
      ring_nf
    have hkey : Real.exp 1 * (α * Real.log t) ≤ Real.exp (α * Real.log t) :=
      exp_one_mul_le_exp hu
    rw [hexp, le_div_iff₀ hα]
    calc Real.exp 1 * Real.log t * α = Real.exp 1 * (α * Real.log t) := by ring
      _ ≤ Real.exp (α * Real.log t) := hkey
end
