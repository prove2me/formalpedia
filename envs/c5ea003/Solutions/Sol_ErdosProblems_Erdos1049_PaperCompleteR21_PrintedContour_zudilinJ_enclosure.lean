-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinJ_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:16:42.759583+00:00
-- url     : https://prove2.me/submissions/677a70e6-e51f-49d6-b162-b8fa23f4135b

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Definitions.Def_ErdosProblems_Erdos1049_MeasureConstantsR10
import Definitions.Def_ErdosProblems_Erdos1049_PaperCompleteR21_PrintedContourConstants
import Theorems.Thm_ErdosProblems_Erdos1049_PaperCompleteR21_PrintedContour_jterm_bracket
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

theorem jterm_1 : (520234257944252983689065 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (1 / 14) (1 / 12) ∧
    zudilinJTerm (1 / 14) (1 / 12) ≤ (520234257944252983730018 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_2 : (130389583445620342664907 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (1 / 7) (1 / 6) ∧
    zudilinJTerm (1 / 7) (1 / 6) ≤ (130389583445620342704788 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_3 : (58270372574725805776611 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (3 / 14) (1 / 4) ∧
    zudilinJTerm (3 / 14) (1 / 4) ≤ (58270372574725805815452 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_4 : (33060256155096201542528 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (2 / 7) (1 / 3) ∧
    zudilinJTerm (2 / 7) (1 / 3) ≤ (33060256155096201580359 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_5 : (16341288387977575824500 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (5 / 14) (2 / 5) ∧
    zudilinJTerm (5 / 14) (2 / 5) ≤ (16341288387977575861453 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_6 : (8871944612662719520212 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (3 / 7) (7 / 15) ∧
    zudilinJTerm (3 / 7) (7 / 15) ≤ (8871944612662719556309 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_7 : (5112396152887661962364 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (1 / 2) (8 / 15) ∧
    zudilinJTerm (1 / 2) (8 / 15) ≤ (5112396152887661997627 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_8 : (3052877839467000279792 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (4 / 7) (3 / 5) ∧
    zudilinJTerm (4 / 7) (3 / 5) ≤ (3052877839467000314241 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_9 : (1851441174764463544560 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (9 / 14) (2 / 3) ∧
    zudilinJTerm (9 / 14) (2 / 3) ≤ (1851441174764463578216 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_10 : (1116095029136323534615 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (5 / 7) (11 / 15) ∧
    zudilinJTerm (5 / 7) (11 / 15) ≤ (1116095029136323567497 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_11 : (648929409578163447514 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (11 / 14) (4 / 5) ∧
    zudilinJTerm (11 / 14) (4 / 5) ≤ (648929409578163479643 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_12 : (343386774024217566531 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (6 / 7) (13 / 15) ∧
    zudilinJTerm (6 / 7) (13 / 15) ≤ (343386774024217597925 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])

theorem jterm_13 : (139015249897499641177 : ℝ) / 10 ^ 22 ≤ zudilinJTerm (13 / 14) (14 / 15) ∧
    zudilinJTerm (13 / 14) (14 / 15) ≤ (139015249897499671854 : ℝ) / 10 ^ 22 :=
  jterm_bracket (by norm_num) (by norm_num)
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
    (by norm_num [tailLow, tailHigh, tailNum, Finset.sum_range_succ])
end ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperCompleteR21 in
open ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour in
theorem solution :
    (77943184475009095899 : ℝ) / 10 ^ 18 ≤ zudilinJ ∧
      zudilinJ ≤ (77943184475009095946 : ℝ) / 10 ^ 18 := by
  have h1 := jterm_1
  have h2 := jterm_2
  have h3 := jterm_3
  have h4 := jterm_4
  have h5 := jterm_5
  have h6 := jterm_6
  have h7 := jterm_7
  have h8 := jterm_8
  have h9 := jterm_9
  have h10 := jterm_10
  have h11 := jterm_11
  have h12 := jterm_12
  have h13 := jterm_13
  unfold zudilinJ
  constructor
  · linarith [h1.1, h2.1, h3.1, h4.1, h5.1, h6.1, h7.1, h8.1, h9.1, h10.1, h11.1, h12.1, h13.1]
  · linarith [h1.2, h2.2, h3.2, h4.2, h5.2, h6.2, h7.2, h8.2, h9.2, h10.2, h11.2, h12.2, h13.2]
