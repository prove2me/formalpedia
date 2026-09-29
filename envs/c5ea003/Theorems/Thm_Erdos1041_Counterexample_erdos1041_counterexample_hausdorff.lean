-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_erdos1041_counterexample_hausdorff
-- name    : Erdos1041.Counterexample.erdos1041_counterexample_hausdorff
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:37:30.370411+00:00
-- url     : https://prove2.me/theorems/9c4392a7-72b0-41e8-9a05-a5369e90ebe6
-- title:
--   A degree-seven lemniscate bottleneck has Hausdorff measure above two
-- statement:
--   For the explicit degree-seven polynomial f at s=10⁻⁶ specified in the accompanying Definitions, every preconnected set K contained in {z∈ℂ:|f(z)|<1} and containing two distinct roots of f has one-dimensional Hausdorff measure greater than 2. In particular this applies to the image of any continuous root-to-root path. The construction is ani’s fixed-parameter example.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L281-L384
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_HausdorffLength
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026. -/

/-!
# Erdős #1041 with length as one-dimensional Hausdorff measure

Formal Conjectures states Erdős #1041 with the length of a path defined as the
one-dimensional Hausdorff measure `μH[1]` of its image. `erdos1041_counterexample`
bounds the total variation of a parametrisation instead. This module proves the
Hausdorff form for the same polynomial `f`, and in a stronger shape: every
preconnected subset of the strict lemniscate `Ω(f)` that contains two distinct
roots has one-dimensional Hausdorff measure greater than two
(`erdos1041_counterexample_hausdorff`). The image of any path joining two roots
is such a set.

The argument reuses the bottleneck geometry of `Bottleneck.lean` and adds no
arc-extraction, rectifiability or length-of-arc lemma. Removing the slit
preimage from the component of `Ω(f)` through the critical point leaves an open
set in which no preconnected subset contains both roots, because the polynomial
restricted there is a covering of a simply connected base. So a preconnected
set `K` through both roots must, for every radius between the slit preimage and
a root, meet the circle of that radius about the critical point inside the
connected component of that root (`bottleneck_sheet_crossing`). The two
components are disjoint open sets, the distance to the critical point is
1-Lipschitz, and on the real line `μH[1]` is Lebesgue measure, so `μH[1] K` is at
least the sum of the two radial lengths (`s3_bottleneck_hausdorff`). That is the
same bound `s3_bottleneck_length` gives for total variation, so the numerical
margin of `Assembly.lean` applies unchanged.

`erdos1041_hausdorff_negation` and `erdos1041_hausdorff_answer_false` state the
Formal Conjectures parent `Erdos1041.erdos_1041` in its own vocabulary, with
`fcLength` its `length`, and refute it.

The mathematics of the counterexample is ani's. The polynomial is the single
member `s = 10⁻⁶` of ani's family fixed in `Defs.lean`.
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Polynomial Metric


/-! ## The slit domain separates the two roots -/





/-! ## Crossing every circle inside each sheet -/



/-! ## From radial crossings to Hausdorff measure -/





/-! ## The instance `f` -/

open Erdos1041.Counterexample

theorem Erdos1041.Counterexample.erdos1041_counterexample_hausdorff :
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K → K ⊆ Omega f →
        (2 : ℝ≥0∞) < μH[1] K := by sorry
