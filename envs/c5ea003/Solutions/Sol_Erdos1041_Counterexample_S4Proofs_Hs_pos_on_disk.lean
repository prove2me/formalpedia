-- Prove2me | solution 1 for Erdos1041.Counterexample.S4Proofs.Hs_pos_on_disk
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:16:37.930297+00:00
-- url     : https://prove2.me/submissions/43024d0e-5a06-4932-8db5-72e85c9a7c0e

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_eps_pow7_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_pos
import Theorems.Thm_Erdos1041_Counterexample_S4Proofs_rho_pow14_le_one
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

noncomputable section
open scoped ComplexConjugate NNReal

namespace Erdos1041.Counterexample.S4Proofs
theorem K0_denom_pos : (0 : ℝ) < 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 := by
  have h1 : (0 : ℝ) < (ρ : ℝ) ^ 14 := pow_pos rho_pos 14
  nlinarith [h1, eps_pow7_pos]
theorem K0_nonneg : 0 ≤ K0 := by
  unfold K0
  exact div_nonneg (by linarith [rho_pow14_le_one]) K0_denom_pos.le
end Erdos1041.Counterexample.S4Proofs

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S4Proofs in
theorem solution {v : ℂ} {rr var reLo absHi : ℝ} (habs : 0 ≤ absHi)
    (hvar : ∀ w : ℂ, ‖w - v‖ ≤ rr → ‖Q.eval w - qT0 v‖ ≤ var)
    (hre : reLo ≤ (qT0 v).re)
    (hnorm : ∀ w : ℂ, ‖w - v‖ ≤ rr → ‖Q.eval w‖ ≤ absHi)
    (hpos : 0 < reLo - var - absHi ^ 2 / 10 ^ 80) :
    ∀ w : ℂ, ‖w - v‖ ≤ rr → 0 < Hs w := by
  intro w hw
  have hv := hvar w hw
  have hn := hnorm w hw
  have hrege : (qT0 v).re - (Q.eval w).re ≤ var := by
    have := Complex.abs_re_le_norm (qT0 v - Q.eval w)
    simp only [Complex.sub_re] at this
    calc (qT0 v).re - (Q.eval w).re ≤ |(qT0 v).re - (Q.eval w).re| := le_abs_self _
      _ ≤ ‖qT0 v - Q.eval w‖ := this
      _ = ‖Q.eval w - qT0 v‖ := by rw [← norm_neg]; ring_nf
      _ ≤ var := hv
  have hns : Complex.normSq (Q.eval w) ≤ absHi ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have he7 : ((ε : ℝ)) ^ 7 = 1 / 10 ^ 84 := by unfold ε s; push_cast; norm_num
  have hquad : ((ε : ℝ) ^ 7 / 2) * Complex.normSq (Q.eval w) ≤ absHi ^ 2 / 10 ^ 80 := by
    rw [he7]
    nlinarith [hns, Complex.normSq_nonneg (Q.eval w)]
  unfold Hs
  linarith [K0_nonneg, hrege, hre, hpos, hquad]
