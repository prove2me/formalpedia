-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_s4_instance_critical
-- name    : Erdos1041.Counterexample.s4_instance_critical
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:33:28.195136+00:00
-- url     : https://prove2.me/theorems/1daa0421-fb23-480c-823f-57bb9401c023
-- title:
--   The full critical-point and selected-root certificate
-- statement:
--   There exist zs, distinct zeros b₃,b₆ of f, nonzero â, and h>0: zs is the unique simple derivative zero in Ω(f), 0<|f(zs)|<1 with 1−|f(zs)|≤ρ⁷ε⁷·36/(5·10⁶); |â|≥180ρ⁵ε⁵, the normalized shifted quadratic stays within 1/4 on |z|≤h, and the depth is below |â|h²/4. Also zs lies within ρε/1000 of ρε·(823247/1000000)i; b₃,b₆ lie within ρ/10 of ρexp(6πi/7), ρexp(−2πi/7), respectively; every root is within ρ/10 of some seventh-root center, each selected disk contains only its named root, and |b₃−zs|+|b₆−zs|≥ρ(2+143ε/1000).
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceCritical.lean#L4273-L4308
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

open Erdos1041
open Erdos1041.Counterexample
noncomputable section
open scoped ComplexConjugate NNReal
noncomputable section
open scoped ComplexConjugate NNReal

open Erdos1041.Counterexample

theorem Erdos1041.Counterexample.s4_instance_critical :
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
      (ρ : ℝ) * (2 + (ε : ℝ) * (143 / 1000)) ≤ ‖b₃ - zs‖ + ‖b₆ - zs‖ := by sorry
