-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_erdos1041_counterexample_of_slices
-- name    : Erdos1041.Counterexample.erdos1041_counterexample_of_slices
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:31:34.126224+00:00
-- url     : https://prove2.me/theorems/ff0d4f1d-db1d-42cd-9774-5dc4ad2e1408
-- title:
--   The checked slice obligations imply the degree-seven path obstruction
-- statement:
--   Assume the eight exact source slice obligations for the fixed polynomial f: the two-root critical-point result, bottleneck variation bound, monic degree-seven certificate, open-disc root certificate, root distinctness, unique critical configuration, two root-to-critical joins, and two separating barriers. Then f has the stated properties and every strict-lemniscate path between distinct roots has extended total variation greater than two. The exact quantified slice types remain in the formal signature.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Assembly.lean#L109-L315
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

open Erdos1041
open Erdos1041.Counterexample
noncomputable section
open scoped ComplexConjugate ENNReal

open Erdos1041.Counterexample

theorem Erdos1041.Counterexample.erdos1041_counterexample_of_slices
    (hS2 :
      ∀ (p : Polynomial ℂ) (hp : 0 < p.natDegree) (z : ℂ) (hz : z ∈ Omega p)
          (w₁ w₂ : ℂ) (hw₁ : w₁ ∈ connectedComponentIn (Omega p) z)
          (hw₂ : w₂ ∈ connectedComponentIn (Omega p) z) (hne : w₁ ≠ w₂)
          (hr₁ : p.IsRoot w₁) (hr₂ : p.IsRoot w₂),
      ∃ cc ∈ connectedComponentIn (Omega p) z, (Polynomial.derivative p).IsRoot cc)
    (hS3 :
      ∀ (p : Polynomial ℂ) (cc : ℂ) (hcc : cc ∈ Omega p)
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
          (hγmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ connectedComponentIn (Omega p) cc),
      ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 8 / 3 * Real.sqrt (δ / ‖aHat‖))
            ≤ pathLength γ)
    (hS4degree :
      f.Monic ∧ f.natDegree = 7)
    (hS4circle :
      ∀ z, f.IsRoot z → ‖z‖ = (ρ : ℝ))
    (hS4nodup :
      f.roots.Nodup)
    (hS4critical :
      ∃ (zs b₃ b₆ aHat : ℂ) (h : ℝ),
            zs ∈ Omega f ∧
            (Polynomial.derivative f).IsRoot zs ∧
            Polynomial.rootMultiplicity zs (Polynomial.derivative f) = 1 ∧
            (∀ c' ∈ Omega f, (Polynomial.derivative f).IsRoot c' → c' = zs) ∧
            0 < ‖f.eval zs‖ ∧
            0 < 1 - ‖f.eval zs‖ ∧
            1 - ‖f.eval zs‖ ≤ (ρ : ℝ) ^ 7 * (ε : ℝ) ^ 7 * (36 / 5 / 10 ^ 6) ∧
            aHat ≠ 0 ∧ 0 < h ∧
            180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ ∧
            (∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad f zs).eval z / aHat - 1‖ ≤ 1 / 4) ∧
            1 - ‖f.eval zs‖ < ‖aHat‖ * h ^ 2 / 4 ∧
            ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
              < (ρ : ℝ) * (ε : ℝ) / 1000 ∧
            f.IsRoot b₃ ∧ f.IsRoot b₆ ∧ b₃ ≠ b₆ ∧
            ‖b₃ - (ρ : ℂ) * Complex.exp (6 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 ∧
            ‖b₆ - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 ∧
            (∀ w, f.IsRoot w → ∃ j : Fin 7, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10) ∧
            (∀ w, f.IsRoot w →
              ‖w - (ρ : ℂ) * Complex.exp (6 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 →
              w = b₃) ∧
            (∀ w, f.IsRoot w →
              ‖w - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 →
              w = b₆) ∧
            (ρ : ℝ) * (2 + (ε : ℝ) * (143 / 1000)) ≤ ‖b₃ - zs‖ + ‖b₆ - zs‖)
    (hS5 :
      ∀ (zs b₃ b₆ : ℂ) (hzs : zs ∈ Omega f)
          (hcrit : (Polynomial.derivative f).IsRoot zs)
          (hr₃ : f.IsRoot b₃) (hr₆ : f.IsRoot b₆)
          (hnear₃ : ‖b₃ - (ρ : ℂ) * Complex.exp (6 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10)
          (hnear₆ : ‖b₆ - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10),
      b₃ ∈ connectedComponentIn (Omega f) zs ∧ b₆ ∈ connectedComponentIn (Omega f) zs)
    (hS7 :
      ∀ (zs : ℂ)
          (hnear : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
            < (ρ : ℝ) * (ε : ℝ) / 1000),
      ∃ g₁ g₂ : ℂ → ℝ, Continuous g₁ ∧ Continuous g₂ ∧
            (∀ z, g₁ z = 0 → 1 ≤ ‖f.eval z‖) ∧ (∀ z, g₂ z = 0 → 1 ≤ ‖f.eval z‖) ∧
            g₁ zs < 0 ∧ g₂ zs < 0 ∧
            (∀ j : Fin 7, j.val = 0 ∨ j.val = 1 ∨ j.val = 2 →
              ∀ w, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10 → 0 < g₁ w) ∧
            (∀ j : Fin 7, j.val = 4 ∨ j.val = 5 →
              ∀ w, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10 → 0 < g₂ w)) :
    f.Monic ∧ f.natDegree = 7 ∧
    (∀ z, f.IsRoot z → ‖z‖ < 1) ∧
    f.roots.Nodup ∧
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) → γ 0 = z₁ → γ 1 = z₂ →
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖f.eval (γ τ)‖ < 1) →
        (2 : ENNReal) < pathLength γ := by sorry
