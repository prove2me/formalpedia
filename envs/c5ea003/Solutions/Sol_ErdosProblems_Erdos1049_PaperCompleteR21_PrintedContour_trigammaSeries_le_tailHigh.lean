-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.trigammaSeries_le_tailHigh
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:13:48.407362+00:00
-- url     : https://prove2.me/submissions/6a61f40c-0c33-4dce-8db8-2f01faab7981

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Definitions.Def_ErdosProblems_Erdos1049_MeasureConstantsR10
import Definitions.Def_ErdosProblems_Erdos1049_PaperCompleteR21_PrintedContourConstants
import Theorems.Thm_ErdosProblems_Erdos1049_BezoutPluckerJets_bezoutPluckerEquiv_apply
import Theorems.Thm_ErdosProblems_Erdos1049_summable_trigammaTerm
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.ZetaValues
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Erdős #1049: the printed decimals of `θ*`, `μ` and `4^μ`

`res:rational-base-threshold`, `long1049:res:region` and `long1049:res:31over4`
print three truncated decimal constants built from Zudilin's trigamma constant

`J = ∑_{i=1}^{13} (ψ₁(uᵢ) - ψ₁(vᵢ))`,  `C₀ = 266 - (3/π²)(225 - J)`,
`C₁ = 1091/2`,  `θ* = C₀/C₁`,  `μ = C₁/C₀`:

* `θ* = 0.40568302138406054…` (the long paper; `0.4056830213840605…` in the
  short paper);
* `μ = 2.4649786835749750…`;
* `4^μ = 30.483515…`.

Pinning seventeen digits of `θ*` needs `J` to about `10^{-15}`, which the
`k = 0` and sixteen-term partial sums already in the tree cannot give.  The
tool built here is a closed two-sided rational bracket for the trigamma series,

`tailLow x ≤ ψ₁(x) ≤ tailHigh x`  for `x ≥ 1`,

with `tailLow x = (1/x + 1/(2x²) + 1/(6x³) - 1/(30x⁵) + 1/(42x⁷) - 1/(30x⁹))`
and `tailHigh x = tailLow x + 5/(66x¹¹)`.  Both are proved from scratch by an
exact telescoping certificate: the rational function `tailLow x - tailLow (x+1)
- 1/x²` has numerator `-(1925x¹⁰ + 9625x⁹ + 21274x⁸ + 27346x⁷ + 22462x⁶
+ 12100x⁵ + 4180x⁴ + 847x³ + 77x²)` over `2310x¹¹(x+1)¹¹`, hence is `≤ 0`, and
the corresponding numerator for `tailHigh` is `7601x⁸ + 30404x⁷ + 58388x⁶
+ 68750x⁵ + 53570x⁴ + 28028x³ + 9548x² + 1925x + 175 ≥ 0`.  No Euler–Maclaurin
theory, no Bernoulli numbers and no `native_decide` are used: the two
polynomials are single-signed for every `x > 0`, so telescoping the step
inequality bounds every partial sum.

Splitting each `ψ₁` off after thirty-two exact rational terms then gives each
of the thirteen differences to about `4 · 10^{-18}`, hence `J` to `5 · 10^{-17}`
and `θ*` to `3 · 10^{-20}`, which is thirty times the margin needed for the
seventeenth printed digit.  The value of `π` comes from `Real.pi_gt_d20` /
`Real.pi_lt_d20`, and `log 2` from Mathlib's Taylor estimate for `log (1 - x)`.
-/

namespace ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! ## A closed rational bracket for the trigamma series -/









theorem tailHigh_step {x : ℝ} (hx : 0 < x) : 1 / x ^ 2 ≤ tailHigh x - tailHigh (x + 1) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hxne : x ≠ 0 := hx.ne'
  have hx1ne : x + 1 ≠ 0 := hx1.ne'
  have hden : (0 : ℝ) < 2310 * x ^ 11 * (x + 1) ^ 11 :=
    mul_pos (mul_pos (by norm_num) (pow_pos hx 11)) (pow_pos hx1 11)
  have hnum : (0 : ℝ) ≤ 7601 * x ^ 8 + 30404 * x ^ 7 + 58388 * x ^ 6 + 68750 * x ^ 5 +
      53570 * x ^ 4 + 28028 * x ^ 3 + 9548 * x ^ 2 + 1925 * x + 175 := by
    have p2 := pow_pos hx 2
    have p3 := pow_pos hx 3
    have p4 := pow_pos hx 4
    have p5 := pow_pos hx 5
    have p6 := pow_pos hx 6
    have p7 := pow_pos hx 7
    have p8 := pow_pos hx 8
    linarith
  have key : tailHigh x - tailHigh (x + 1) - 1 / x ^ 2 =
      (7601 * x ^ 8 + 30404 * x ^ 7 + 58388 * x ^ 6 + 68750 * x ^ 5 + 53570 * x ^ 4 +
        28028 * x ^ 3 + 9548 * x ^ 2 + 1925 * x + 175)
        / (2310 * x ^ 11 * (x + 1) ^ 11) := by
    unfold tailHigh tailNum
    field_simp
    ring
  have hge : (0 : ℝ) ≤ tailHigh x - tailHigh (x + 1) - 1 / x ^ 2 := by
    rw [key]; exact div_nonneg hnum hden.le
  linarith

theorem tailHigh_nonneg {y : ℝ} (hy : 1 ≤ y) : 0 ≤ tailHigh y := by
  have hy0 : (0 : ℝ) < y := by linarith
  have ht : (0 : ℝ) ≤ y - 1 := by linarith
  have hexp : tailNum y + 175 =
      2310 * (y - 1) ^ 10 + 24255 * (y - 1) ^ 9 + 114730 * (y - 1) ^ 8 +
        321860 * (y - 1) ^ 7 + 592823 * (y - 1) ^ 6 + 748748 * (y - 1) ^ 5 +
        656480 * (y - 1) ^ 4 + 394460 * (y - 1) ^ 3 + 155408 * (y - 1) ^ 2 +
        36179 * (y - 1) + 3926 := by
    unfold tailNum; ring
  unfold tailHigh
  refine div_nonneg ?_ ?_
  · rw [hexp]
    linarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
      pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9, pow_nonneg ht 10]
  · linarith [pow_pos hy0 11]
end ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperCompleteR21 in
open ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour in
theorem solution {x : ℝ} (hx : 1 ≤ x) : trigammaSeries x ≤ tailHigh x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have tel : ∀ n : ℕ, ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + x) ^ 2 ≤
      tailHigh x - tailHigh (x + (n : ℝ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hxn : (0 : ℝ) < x + (n : ℝ) := by linarith
      have hstep := tailHigh_step hxn
      have hterm : (1 : ℝ) / ((n : ℝ) + x) ^ 2 = 1 / (x + (n : ℝ)) ^ 2 := by ring
      have harg : x + ((n + 1 : ℕ) : ℝ) = x + (n : ℝ) + 1 := by push_cast; ring
      rw [Finset.sum_range_succ, harg, hterm]
      linarith
  have hb : ∀ n : ℕ, ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + x) ^ 2 ≤ tailHigh x := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (0 : ℝ) ≤ tailHigh (x + (n : ℝ)) := tailHigh_nonneg (by linarith)
    linarith [tel n]
  have hsum := summable_trigammaTerm hx0
  have hts := hsum.hasSum.tendsto_sum_nat
  exact le_of_tendsto hts (Filter.Eventually.of_forall hb)
