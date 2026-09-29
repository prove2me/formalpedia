-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_s3_bottleneck_length
-- name    : Erdos1041.Counterexample.s3_bottleneck_length
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:32:02.909676+00:00
-- url     : https://prove2.me/theorems/7a952009-9215-48b6-970d-e64947efa2b2
-- title:
--   A quadratic bottleneck gives the variation lower bound
-- statement:
--   Let p be a complex polynomial and cc a nonzero-value critical point in Ω(p). Suppose distinct roots b₁,b₂ lie in cc’s component, are the only roots there, and cc is its only critical point and is a simple derivative root. Let aHat be nonzero and h>0, with the normalized shifted quadratic within 1/4 of 1 on |z|≤h. Set δ=1−|p(cc)|, assume δ>0 and δ<|aHat|h²/4. Then every path continuous on [0,1], joining b₁ to b₂ and staying in that component, has extended total variation at least ENNReal.ofReal(|b₁−cc|+|b₂−cc|−(8/3)√(δ/|aHat|)).
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L1549-L1583
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

theorem Erdos1041.Counterexample.s3_bottleneck_length
    (p : Polynomial ℂ) (cc : ℂ) (hcc : cc ∈ Omega p)
    (hcrit : (Polynomial.derivative p).IsRoot cc)
    (hv : p.eval cc ≠ 0)
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (hsimple : Polynomial.rootMultiplicity cc (Polynomial.derivative p) = 1)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (γ : ℝ → ℂ) (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
    (hγmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ connectedComponentIn (Omega p) cc) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 8 / 3 * Real.sqrt (δ / ‖aHat‖))
      ≤ pathLength γ := by sorry
