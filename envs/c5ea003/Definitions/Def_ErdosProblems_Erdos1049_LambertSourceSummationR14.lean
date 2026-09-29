-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_LambertSourceSummationR14
-- name    : ErdosProblems_Erdos1049_LambertSourceSummationR14
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:47:46.047079+00:00
-- url     : https://prove2.me/theorems/8e188ed6-084d-41d7-aef1-3fb597d54065
-- title:
--   Absolutely convergent Lambert-window summation for the literal source B
-- statement:
--   Absolute convergence permits the finite Lambert-window correction and pole series to be rearranged, identifying the correction exactly with the literal B expression. The submitted module contains the source declarations lambertQTerm, lambertQ, lambertWindowTerm, lambertWindow, lambertWindowTerm_nonneg, among others. Source topic: Absolutely convergent Lambert-window summation for the literal source B.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/LambertSourceSummationR14.lean#L23-L261
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
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
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Absolutely convergent Lambert-window summation for the literal source B

Proves A_n F - B_n equals the absolutely convergent pole series.

The finite correction terms are exactly those of `sourceBReal`, not a newly
chosen constant term. All geometric and Lambert sums below have a summability
proof before `tsum` is used. The terminal theorem identifies A*F-B with the
actual partial-fraction series. The separate residue/interpolation calculation
must still identify that series with the positive hypergeometric H.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset
open PaperR10 PaperR11 PaperR12
open scoped BigOperators

noncomputable def lambertQTerm (q : ℝ) (t : ℕ) : ℝ :=
  q ^ (t + 1) / (1 - q ^ (t + 1))
noncomputable def lambertQ (q : ℝ) : ℝ := ∑' t : ℕ, lambertQTerm q t

noncomputable def lambertWindowTerm (q : ℝ) (a c t : ℕ) : ℝ :=
  q ^ ((a + 1) * (c + 1 + t)) / (1 - q ^ (c + 1 + t))
noncomputable def lambertWindow (q : ℝ) (a c : ℕ) : ℝ :=
  ∑' t : ℕ, lambertWindowTerm q a c t































/-- Literal residues multiplied by their shifted pole tails. This definition
retains the exact A_s already used to define the source polynomials. -/
noncomputable def sourcePoleSeriesTerm (q : ℝ) (n t : ℕ) : ℝ :=
  ∑ s ∈ range (13 * n + 1),
    (sourceASummand n s).eval₂ (Int.castRingHom ℝ) q⁻¹ *
      lambertWindowTerm q (14 * n) (2 * n + s) t

noncomputable def sourcePoleSeries (q : ℝ) (n : ℕ) : ℝ :=
  ∑' t : ℕ, sourcePoleSeriesTerm q n t





end ErdosProblems.Erdos1049.PaperR14


