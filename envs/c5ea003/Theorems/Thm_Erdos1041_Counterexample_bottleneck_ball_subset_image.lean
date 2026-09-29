-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_bottleneck_ball_subset_image
-- name    : Erdos1041.Counterexample.bottleneck_ball_subset_image
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:25:32.388708+00:00
-- url     : https://prove2.me/theorems/29e5c0c5-b40d-4c90-ab9b-f65fc9491070
-- title:
--   A boundary displacement forces ball coverage
-- statement:
--   Let f be continuous on a closed disk and suppose its open-disk image is open. If every boundary point moves at least ε away from f(c), then the ε-ball around f(c) lies in the image of the open disk.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L584-L625
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation

open Erdos1041
open Erdos1041.Counterexample
noncomputable section
open Topology

open Erdos1041.Counterexample

theorem Erdos1041.Counterexample.bottleneck_ball_subset_image (f : ℂ → ℂ) (c : ℂ) (r ε : ℝ) (hr : 0 < r)
    (hcont : ContinuousOn f (Metric.closedBall c r))
    (himg : IsOpen (f '' Metric.ball c r))
    (hsphere : ∀ z ∈ Metric.sphere c r, ε ≤ ‖f z - f c‖) :
    Metric.ball (f c) ε ⊆ f '' Metric.ball c r := by sorry
