-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_bottleneck_critical_fibre_singleton
-- name    : Erdos1041.Counterexample.bottleneck_critical_fibre_singleton
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:27:32.093569+00:00
-- url     : https://prove2.me/theorems/9dc9e15e-e943-4529-8d3e-459a22129471
-- title:
--   The critical fiber has only its critical point
-- statement:
--   With two roots and a unique critical point in the component under the source disk and covering conditions, any component point z satisfying p(z)=p(cc) must equal cc.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L1353-L1463
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

theorem Erdos1041.Counterexample.bottleneck_critical_fibre_singleton (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (aHat : ℂ) (haHat : aHat ≠ 0) (h s δ : ℝ) (hh : 0 < h) (hs : 0 < s)
    (hsh : 5 / 4 * s < h) (hsδ : ‖aHat‖ * s ^ 2 ≤ δ) (hδ : δ = 1 - ‖p.eval cc‖)
    (hδpos : 0 < δ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (b₁ b₂ : ℂ)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (z : ℂ) (hz : z ∈ connectedComponentIn (Omega p) cc) (hpz : p.eval z = p.eval cc) :
    z = cc := by sorry
