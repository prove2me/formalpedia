-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_bottleneck_two_local_preimages
-- name    : Erdos1041.Counterexample.bottleneck_two_local_preimages
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:27:23.837473+00:00
-- url     : https://prove2.me/theorems/097f5102-77af-4559-b764-fae2bb7f3542
-- title:
--   The quadratic critical value has two local preimages
-- statement:
--   Under the source disk criterion and a sufficiently small nonzero η, p(cc)+aHat η² has two distinct preimages in cc’s lemniscate component, each within 5|η|/4 of cc.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L1304-L1351
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

theorem Erdos1041.Counterexample.bottleneck_two_local_preimages (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h s δ : ℝ) (hh : 0 < h) (hs : 0 < s)
    (hsh : 5 / 4 * s < h) (hsδ : ‖aHat‖ * s ^ 2 ≤ δ) (hδ : δ = 1 - ‖p.eval cc‖)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (η : ℂ) (hη : η ≠ 0) (hηs : ‖η‖ < s) :
    ∃ x₁ ∈ connectedComponentIn (Omega p) cc, ∃ x₂ ∈ connectedComponentIn (Omega p) cc,
      x₁ ≠ x₂ ∧ p.eval x₁ = p.eval cc + aHat * η ^ 2 ∧
        p.eval x₂ = p.eval cc + aHat * η ^ 2 ∧
        ‖x₁ - cc‖ ≤ 5 / 4 * ‖η‖ ∧ ‖x₂ - cc‖ ≤ 5 / 4 * ‖η‖ := by sorry
