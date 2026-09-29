-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_bottleneck_no_three_preimages
-- name    : Erdos1041.Counterexample.bottleneck_no_three_preimages
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:27:02.39517+00:00
-- url     : https://prove2.me/theorems/a020cc3b-cf54-4c39-9c9e-c0f0bed837a5
-- title:
--   No slit value has three preimages in the component
-- statement:
--   Under the source’s disk criterion, two-root and unique-critical-point hypotheses, a noncritical value on the slit cannot have three distinct preimages in the critical component.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L1188-L1302
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

theorem Erdos1041.Counterexample.bottleneck_no_three_preimages (p : Polynomial ℂ) (cc : ℂ) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (b₁ b₂ : ℂ)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (ξ : ℂ) (hξ : ξ ∈ bottleneckSlit (p.eval cc)) (hξv : ξ ≠ p.eval cc)
    (w₁ w₂ w₃ : ℂ)
    (hw₁ : w₁ ∈ connectedComponentIn (Omega p) cc)
    (hw₂ : w₂ ∈ connectedComponentIn (Omega p) cc)
    (hw₃ : w₃ ∈ connectedComponentIn (Omega p) cc)
    (hp₁ : p.eval w₁ = ξ) (hp₂ : p.eval w₂ = ξ) (hp₃ : p.eval w₃ = ξ)
    (n12 : w₁ ≠ w₂) (n13 : w₁ ≠ w₃) (n23 : w₂ ≠ w₃) : False := by sorry
