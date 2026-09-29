-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_bottleneck_path_meets_slit_of_covering
-- name    : Erdos1041.Counterexample.bottleneck_path_meets_slit_of_covering
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:30:12.287992+00:00
-- url     : https://prove2.me/theorems/7fa6acc9-c942-44e3-a5fe-d92708d4218c
-- title:
--   Any joining path crosses the slit preimage
-- statement:
--   Under the source covering and two-root hypotheses, a continuous path in the critical component joining distinct roots must meet the preimage of the critical-value slit.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L488-L526
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

theorem Erdos1041.Counterexample.bottleneck_path_meets_slit_of_covering
    (p : Polynomial ℂ) (cc : ℂ) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂) (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (γ : ℝ → ℂ) (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
    (hγmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      γ τ ∈ connectedComponentIn (Omega p) cc) :
    ∃ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ connectedComponentIn (Omega p) cc ∩
      (fun z => p.eval z) ⁻¹' bottleneckSlit (p.eval cc) := by sorry
