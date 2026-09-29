-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_bottleneckSlit_iff
-- name    : Erdos1041.Counterexample.bottleneckSlit_iff
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:24:26.215985+00:00
-- url     : https://prove2.me/theorems/51af1867-26a1-414c-bab4-3137b826f927
-- title:
--   Parameterization of the critical-value slit
-- statement:
--   For nonzero v, a complex point w lies on the slit from |v| in the direction of v up to radius one exactly when w=r v/|v| for a real r with |v|≤r<1.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L57-L73
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

theorem Erdos1041.Counterexample.bottleneckSlit_iff (v w : ℂ) (hv : v ≠ 0) :
    w ∈ bottleneckSlit v ↔
      ∃ r : ℝ, ‖v‖ ≤ r ∧ r < 1 ∧
        w = (r : ℂ) * (v / (‖v‖ : ℂ)) := by sorry
