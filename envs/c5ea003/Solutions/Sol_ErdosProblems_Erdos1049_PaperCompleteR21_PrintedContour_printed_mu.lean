-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_mu
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:19:50.202187+00:00
-- url     : https://prove2.me/submissions/e7b51aa7-03f7-4df4-9614-d23769e2c1eb

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Definitions.Def_ErdosProblems_Erdos1049_MeasureConstantsR10
import Definitions.Def_ErdosProblems_Erdos1049_PaperCompleteR21_PrintedContourConstants
import Theorems.Thm_ErdosProblems_Erdos1049_PaperCompleteR21_PrintedContour_zudilinC0_enclosure
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



















/-! ## Splitting off thirty-two exact terms -/





/-! ## The thirteen intervals -/





























/-! ## `π²`, `C₀`, `θ*` and `μ` -/







theorem zudilinC0_pos' : 0 < zudilinC0 := by
  have h := zudilinC0_enclosure.1
  have : (0 : ℝ) < (221300088165005025116 : ℝ) / 10 ^ 18 := by norm_num
  linarith
end ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperCompleteR21 in
open ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour in
theorem solution :
    (24649786835749750 : ℝ) / 10 ^ 16 < paperMu ∧
      paperMu < (24649786835749751 : ℝ) / 10 ^ 16 := by
  have h := zudilinC0_enclosure
  have hc0 : (0 : ℝ) < zudilinC0 := zudilinC0_pos'
  have hC1 : zudilinC1 = 1091 / 2 := rfl
  unfold paperMu
  rw [hC1]
  constructor
  · rw [lt_div_iff₀ hc0]
    have hstep : (24649786835749750 : ℝ) / 10 ^ 16 * zudilinC0 ≤
        (24649786835749750 : ℝ) / 10 ^ 16 * ((221300088165005025132 : ℝ) / 10 ^ 18) :=
      mul_le_mul_of_nonneg_left h.2 (by norm_num)
    have hnum : (24649786835749750 : ℝ) / 10 ^ 16 *
        ((221300088165005025132 : ℝ) / 10 ^ 18) < 1091 / 2 := by norm_num
    linarith
  · rw [div_lt_iff₀ hc0]
    have hstep : (24649786835749751 : ℝ) / 10 ^ 16 *
        ((221300088165005025116 : ℝ) / 10 ^ 18) ≤
        (24649786835749751 : ℝ) / 10 ^ 16 * zudilinC0 :=
      mul_le_mul_of_nonneg_left h.1 (by norm_num)
    have hnum : (1091 : ℝ) / 2 < (24649786835749751 : ℝ) / 10 ^ 16 *
        ((221300088165005025116 : ℝ) / 10 ^ 18) := by norm_num
    linarith
