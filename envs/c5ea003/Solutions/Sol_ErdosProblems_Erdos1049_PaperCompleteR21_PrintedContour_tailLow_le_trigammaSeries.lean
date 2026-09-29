-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailLow_le_trigammaSeries
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:13:47.725578+00:00
-- url     : https://prove2.me/submissions/e44a1849-8c26-413d-a575-eaca46a9f4e0

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







theorem tailLow_step {x : ℝ} (hx : 0 < x) : tailLow x - tailLow (x + 1) ≤ 1 / x ^ 2 := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hxne : x ≠ 0 := hx.ne'
  have hx1ne : x + 1 ≠ 0 := hx1.ne'
  have hden : (0 : ℝ) < 2310 * x ^ 11 * (x + 1) ^ 11 :=
    mul_pos (mul_pos (by norm_num) (pow_pos hx 11)) (pow_pos hx1 11)
  have hnum : (0 : ℝ) ≤ 1925 * x ^ 10 + 9625 * x ^ 9 + 21274 * x ^ 8 + 27346 * x ^ 7 +
      22462 * x ^ 6 + 12100 * x ^ 5 + 4180 * x ^ 4 + 847 * x ^ 3 + 77 * x ^ 2 := by
    have p2 := pow_pos hx 2
    have p3 := pow_pos hx 3
    have p4 := pow_pos hx 4
    have p5 := pow_pos hx 5
    have p6 := pow_pos hx 6
    have p7 := pow_pos hx 7
    have p8 := pow_pos hx 8
    have p9 := pow_pos hx 9
    have p10 := pow_pos hx 10
    linarith
  have key : 1 / x ^ 2 - (tailLow x - tailLow (x + 1)) =
      (1925 * x ^ 10 + 9625 * x ^ 9 + 21274 * x ^ 8 + 27346 * x ^ 7 + 22462 * x ^ 6 +
        12100 * x ^ 5 + 4180 * x ^ 4 + 847 * x ^ 3 + 77 * x ^ 2)
        / (2310 * x ^ 11 * (x + 1) ^ 11) := by
    unfold tailLow tailNum
    field_simp
    ring
  have hge : (0 : ℝ) ≤ 1 / x ^ 2 - (tailLow x - tailLow (x + 1)) := by
    rw [key]; exact div_nonneg hnum hden.le
  linarith





theorem tailLow_le_two_div {y : ℝ} (hy : 1 ≤ y) : tailLow y ≤ 2 / y := by
  have hy0 : (0 : ℝ) < y := by linarith
  have ht : (0 : ℝ) ≤ y - 1 := by linarith
  have hexp : 4620 * y ^ 10 - tailNum y =
      2310 * (y - 1) ^ 10 + 21945 * (y - 1) ^ 9 + 93170 * (y - 1) ^ 8 +
        232540 * (y - 1) ^ 7 + 377377 * (y - 1) ^ 6 + 415492 * (y - 1) ^ 5 +
        313720 * (y - 1) ^ 4 + 159940 * (y - 1) ^ 3 + 52492 * (y - 1) ^ 2 +
        10021 * (y - 1) + 869 := by
    unfold tailNum; ring
  have hnn : (0 : ℝ) ≤ 4620 * y ^ 10 - tailNum y := by
    rw [hexp]
    linarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
      pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9, pow_nonneg ht 10]
  have hyne : y ≠ 0 := hy0.ne'
  have hd : (0 : ℝ) < 2310 * y ^ 11 := by linarith [pow_pos hy0 11]
  have key : 2 / y - tailLow y = (4620 * y ^ 10 - tailNum y) / (2310 * y ^ 11) := by
    unfold tailLow
    first
      | (field_simp; ring)
      | field_simp
  have hge : (0 : ℝ) ≤ 2 / y - tailLow y := by
    rw [key]; exact div_nonneg hnn hd.le
  linarith
end ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperCompleteR21 in
open ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour in
theorem solution {x : ℝ} (hx : 1 ≤ x) : tailLow x ≤ trigammaSeries x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsum := summable_trigammaTerm hx0
  have tel : ∀ n : ℕ, tailLow x - tailLow (x + (n : ℝ)) ≤
      ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + x) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hxn : (0 : ℝ) < x + (n : ℝ) := by linarith
      have hstep := tailLow_step hxn
      have hterm : (1 : ℝ) / ((n : ℝ) + x) ^ 2 = 1 / (x + (n : ℝ)) ^ 2 := by ring
      have harg : x + ((n + 1 : ℕ) : ℝ) = x + (n : ℝ) + 1 := by push_cast; ring
      rw [Finset.sum_range_succ, harg, hterm]
      linarith
  have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + x) ^ 2 ≤ trigammaSeries x := by
    intro n
    exact hsum.sum_le_tsum (Finset.range n) (fun k _ => by positivity)
  by_contra hcon
  push_neg at hcon
  have hdpos : (0 : ℝ) < tailLow x - trigammaSeries x := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / (tailLow x - trigammaSeries x))
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (div_pos (by norm_num) hdpos) hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := hnpos.le
  have hxn1 : (1 : ℝ) ≤ x + (n : ℝ) := by linarith
  have hxn0 : (0 : ℝ) < x + (n : ℝ) := by linarith
  have hbd := tailLow_le_two_div hxn1
  have hkey : tailLow x - trigammaSeries x ≤ 2 / (x + (n : ℝ)) := by
    linarith [tel n, hpart n]
  rw [le_div_iff₀ hxn0] at hkey
  rw [div_lt_iff₀ hdpos] at hn
  nlinarith [mul_pos hdpos hx0]
