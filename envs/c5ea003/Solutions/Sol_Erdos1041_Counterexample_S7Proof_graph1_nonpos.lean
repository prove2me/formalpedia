-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.graph1_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T23:50:04.823895+00:00
-- url     : https://prove2.me/submissions/2f38b7ea-b51d-4bd6-b12d-426a39244a7d

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_cert_tail_A
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_cert_tail_B
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_phi1_region_0
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_phi1_region_1
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_phi1_region_2
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_phi1_region_3
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_phi1_region_4
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_phi1_region_5
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_segment_g1_01
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_segment_g1_12
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_segment_g1_23
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_segment_g1_34
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

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Explicit separating barriers replacing the Riemann-Hurwitz step of Lemma 2.1, at `s = 10⁻⁶`. -/

noncomputable section

namespace Erdos1041.Counterexample.S7Proof
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (x : ℝ) : Hcoord x (phi1 x) ≤ 0 := by
  by_cases h0 : 250 ≤ x
  ·
    rw [phi1_region_0 x h0]
    have hr : 0 ≤ (x / 40 - (25 / 4)) := by linarith
    have hx : (-5 * x + 4 * (((9 / 40) * x))) / 41 = (-25) + ((-29) - (-25)) * (x / 40 - (25 / 4)) := by ring
    have hy : (4 * x + 5 * (((9 / 40) * x))) / 41 = (125 / 4) + ((145 / 4) - (125 / 4)) * (x / 40 - (25 / 4)) := by ring
    unfold Hcoord
    rw [hx, hy]
    exact cert_tail_A (x / 40 - (25 / 4)) hr
  ·
    by_cases h1 : (519 / 10) ≤ x
    ·
      have hxhi : x ≤ 250 := by linarith
      rw [phi1_region_1 x h1 hxhi]
      unfold l1_01
      have hr0 : 0 ≤ ((250 - x) / (1981 / 10)) := by norm_num; linarith
      have hr1 : ((250 - x) / (1981 / 10)) ≤ 1 := by norm_num; linarith
      have hx : (-5 * x + 4 * (((955 / 3962) * x + (-31775 / 7924)))) / 41 = (-25) + ((-11 / 2) - (-25)) * ((250 - x) / (1981 / 10)) := by ring
      have hy : (4 * x + 5 * (((955 / 3962) * x + (-31775 / 7924)))) / 41 = (125 / 4) + ((61 / 10) - (125 / 4)) * ((250 - x) / (1981 / 10)) := by ring
      unfold Hcoord
      rw [hx, hy]
      exact segment_g1_01 ((250 - x) / (1981 / 10)) hr0 hr1
    ·
      by_cases h2 : (3615717603167 / 500000000000) ≤ x
      ·
        have hxhi : x ≤ (519 / 10) := by linarith
        rw [phi1_region_2 x h2 hxhi]
        unfold l1_12
        have hr0 : 0 ≤ (((519 / 10) - x) / (22334282396833 / 500000000000)) := by norm_num; linarith
        have hr1 : (((519 / 10) - x) / (22334282396833 / 500000000000)) ≤ 1 := by norm_num; linarith
        have hx : (-5 * x + 4 * (((-539296338829 / 44668564793666) * x + (4076722807313861 / 446685647936660)))) / 41 = (-11 / 2) + ((113703 / 500000000000) - (-11 / 2)) * (((519 / 10) - x) / (22334282396833 / 500000000000)) := by ring
        have hy : (4 * x + 5 * (((-539296338829 / 44668564793666) * x + (4076722807313861 / 446685647936660)))) / 41 = (61 / 10) + ((1807859085841 / 1000000000000) - (61 / 10)) * (((519 / 10) - x) / (22334282396833 / 500000000000)) := by ring
        unfold Hcoord
        rw [hx, hy]
        exact segment_g1_12 (((519 / 10) - x) / (22334282396833 / 500000000000)) hr0 hr1
      ·
        by_cases h3 : (-717965515391 / 40000000000) ≤ x
        ·
          have hxhi : x ≤ (3615717603167 / 500000000000) := by linarith
          rw [phi1_region_3 x h3 hxhi]
          unfold l1_23
          have hr0 : 0 ≤ (((3615717603167 / 500000000000) - x) / (25180573091109 / 1000000000000)) := by norm_num; linarith
          have hr1 : (((3615717603167 / 500000000000) - x) / (25180573091109 / 1000000000000)) ≤ 1 := by norm_num; linarith
          have hx : (-5 * x + 4 * (((-1220013986006 / 25180573091109) * x + (47287422848540256709986673 / 5036114618221800000000000)))) / 41 = (113703 / 500000000000) + ((637965515723 / 200000000000) - (113703 / 500000000000)) * (((3615717603167 / 500000000000) - x) / (25180573091109 / 1000000000000)) := by ring
          have hy : (4 * x + 5 * (((-1220013986006 / 25180573091109) * x + (47287422848540256709986673 / 5036114618221800000000000)))) / 41 = (1807859085841 / 1000000000000) + ((-19999999917 / 40000000000) - (1807859085841 / 1000000000000)) * (((3615717603167 / 500000000000) - x) / (25180573091109 / 1000000000000)) := by ring
          unfold Hcoord
          rw [hx, hy]
          exact segment_g1_23 (((3615717603167 / 500000000000) - x) / (25180573091109 / 1000000000000)) hr0 hr1
        ·
          by_cases h4 : (-224) ≤ x
          ·
            have hxhi : x ≤ (-717965515391 / 40000000000) := by linarith
            rw [phi1_region_4 x h4 hxhi]
            unfold l1_34
            have hr0 : 0 ≤ (((-717965515391 / 40000000000) - x) / (8242034484609 / 40000000000)) := by norm_num; linarith
            have hr1 : (((-717965515391 / 40000000000) - x) / (8242034484609 / 40000000000)) ≤ 1 := by norm_num; linarith
            have hx : (-5 * x + 4 * (((-7548137935033 / 41210172423045) * x + (287305378858768 / 41210172423045)))) / 41 = (637965515723 / 200000000000) + (32 - (637965515723 / 200000000000)) * (((-717965515391 / 40000000000) - x) / (8242034484609 / 40000000000)) := by ring
            have hy : (4 * x + 5 * (((-7548137935033 / 41210172423045) * x + (287305378858768 / 41210172423045)))) / 41 = (-19999999917 / 40000000000) + ((-16) - (-19999999917 / 40000000000)) * (((-717965515391 / 40000000000) - x) / (8242034484609 / 40000000000)) := by ring
            unfold Hcoord
            rw [hx, hy]
            exact segment_g1_34 (((-717965515391 / 40000000000) - x) / (8242034484609 / 40000000000)) hr0 hr1
          ·
            have hxlo : x ≤ (-224) := by linarith
            rw [phi1_region_5 x hxlo]
            have hr : 0 ≤ (x / (-14) - 16) := by linarith
            have hx : (-5 * x + 4 * (((-3 / 14) * x))) / 41 = 32 + (34 - 32) * (x / (-14) - 16) := by ring
            have hy : (4 * x + 5 * (((-3 / 14) * x))) / 41 = (-16) + ((-17) - (-16)) * (x / (-14) - 16) := by ring
            unfold Hcoord
            rw [hx, hy]
            exact cert_tail_B (x / (-14) - 16) hr
