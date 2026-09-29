-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperCompleteR21_PrintedContour_trigammaSeries_le_tailHigh
-- name    : ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.trigammaSeries_le_tailHigh
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:04:58.77199+00:00
-- url     : https://prove2.me/theorems/83ee571f-bc74-4660-91bd-1f376e98f5de
-- title:
--   Trigamma series le tail high
-- statement:
--   For every real x≥1, the trigamma series ∑ₖ≥₀ 1/(k+x)² is at most the explicit upper tail bound tailHigh(x).
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L155-L178
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Definitions.Def_ErdosProblems_Erdos1049_MeasureConstantsR10
import Definitions.Def_ErdosProblems_Erdos1049_PaperCompleteR21_PrintedContourConstants
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


set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! ## A closed rational bracket for the trigamma series -/

open ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour

theorem ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.trigammaSeries_le_tailHigh {x : ℝ} (hx : 1 ≤ x) : trigammaSeries x ≤ tailHigh x := by sorry
