-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.graph2_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:21:27.480515+00:00
-- url     : https://prove2.me/submissions/a196470f-97ba-4bbc-9a19-75aa8b048559

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_cert_tail_C
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_cert_tail_D
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_segment_g2_01
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_segment_g2_12
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_segment_g2_23
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
























































theorem phi2_region_0 (x : ℝ) (hlo : 220 ≤ x) :
    phi2 x = (4 / 5) * x := by
  unfold phi2 l2_01 l2_12 l2_23
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi2_region_1 (x : ℝ) (hlo : (2789827582819 / 200000000000) ≤ x) (hhi : x ≤ 220) :
    phi2 x = l2_01 x := by
  unfold phi2 l2_01 l2_12 l2_23
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi2_region_2 (x : ℝ) (hlo : (-2811972559113 / 200000000000) ≤ x) (hhi : x ≤ (2789827582819 / 200000000000)) :
    phi2 x = l2_12 x := by
  unfold phi2 l2_01 l2_12 l2_23
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi2_region_3 (x : ℝ) (hlo : (-230) ≤ x) (hhi : x ≤ (-2811972559113 / 200000000000)) :
    phi2 x = l2_23 x := by
  unfold phi2 l2_01 l2_12 l2_23
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem phi2_region_4 (x : ℝ) (hhi : x ≤ (-230)) :
    phi2 x = (-37 / 46) * x := by
  unfold phi2 l2_01 l2_12 l2_23
  simp only [max_def, min_def]
  split_ifs <;> linarith
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (x : ℝ) : Hcoord x (-phi2 x) ≤ 0 := by
  by_cases h0 : 220 ≤ x
  ·
    rw [phi2_region_0 x h0]
    have hr : 0 ≤ (x / 5 - 44) := by linarith
    have hx : (-5 * x + 4 * (-((4 / 5) * x))) / 41 = (-44) + ((-45) - (-44)) * (x / 5 - 44) := by ring
    have hy : (4 * x + 5 * (-((4 / 5) * x))) / 41 = 0 + (0 - 0) * (x / 5 - 44) := by ring
    unfold Hcoord
    rw [hx, hy]
    exact cert_tail_C (x / 5 - 44) hr
  ·
    by_cases h1 : (2789827582819 / 200000000000) ≤ x
    ·
      have hxhi : x ≤ 220 := by linarith
      rw [phi2_region_1 x h1 hxhi]
      unfold l2_01
      have hr0 : 0 ≤ ((220 - x) / (41210172417181 / 200000000000)) := by norm_num; linarith
      have hr1 : ((220 - x) / (41210172417181 / 200000000000)) ≤ 1 := by norm_num; linarith
      have hx : (-5 * x + 4 * (-((160740689651709 / 206050862085905) * x + (180400000748660 / 41210172417181)))) / 41 = (-44) + ((-3189827584479 / 1000000000000) - (-44)) * ((220 - x) / (41210172417181 / 200000000000)) := by ring
      have hy : (4 * x + 5 * (-((160740689651709 / 206050862085905) * x + (180400000748660 / 41210172417181)))) / 41 = 0 + ((-20000000083 / 40000000000) - 0) * ((220 - x) / (41210172417181 / 200000000000)) := by ring
      unfold Hcoord
      rw [hx, hy]
      exact segment_g2_01 ((220 - x) / (41210172417181 / 200000000000)) hr0 hr1
    ·
      by_cases h2 : (-2811972559113 / 200000000000) ≤ x
      ·
        have hxhi : x ≤ (2789827582819 / 200000000000) := by linarith
        rw [phi2_region_2 x h2 hxhi]
        unfold l2_12
        have hr0 : 0 ≤ (((2789827582819 / 200000000000) - x) / (1400450035483 / 50000000000)) := by norm_num; linarith
        have hr1 : (((2789827582819 / 200000000000) - x) / (1400450035483 / 50000000000)) ≤ 1 := by norm_num; linarith
        have hx : (-5 * x + 4 * (-((-578879533802 / 7002250177415) * x + (22984875809240463303357391 / 1400450035483000000000000)))) / 41 = (-3189827584479 / 1000000000000) + ((1069 / 1000000000000) - (-3189827584479 / 1000000000000)) * (((2789827582819 / 200000000000) - x) / (1400450035483 / 50000000000)) := by ring
        have hy : (4 * x + 5 * (-((-578879533802 / 7002250177415) * x + (22984875809240463303357391 / 1400450035483000000000000)))) / 41 = (-20000000083 / 40000000000) + ((-702993139511 / 200000000000) - (-20000000083 / 40000000000)) * (((2789827582819 / 200000000000) - x) / (1400450035483 / 50000000000)) := by ring
        unfold Hcoord
        rw [hx, hy]
        exact segment_g2_12 (((2789827582819 / 200000000000) - x) / (1400450035483 / 50000000000)) hr0 hr1
      ·
        by_cases h3 : (-230) ≤ x
        ·
          have hxhi : x ≤ (-2811972559113 / 200000000000) := by linarith
          rw [phi2_region_3 x h3 hxhi]
          unfold l2_23
          have hr0 : 0 ≤ (((-2811972559113 / 200000000000) - x) / (43188027440887 / 200000000000)) := by norm_num; linarith
          have hr1 : (((-2811972559113 / 200000000000) - x) / (43188027440887 / 200000000000)) ≤ 1 := by norm_num; linarith
          have hx : (-5 * x + 4 * (-((-167425171516501 / 215940137204435) * x + (288227186805049 / 43188027440887)))) / 41 = (1069 / 1000000000000) + (10 - (1069 / 1000000000000)) * (((-2811972559113 / 200000000000) - x) / (43188027440887 / 200000000000)) := by ring
          have hy : (4 * x + 5 * (-((-167425171516501 / 215940137204435) * x + (288227186805049 / 43188027440887)))) / 41 = (-702993139511 / 200000000000) + ((-45) - (-702993139511 / 200000000000)) * (((-2811972559113 / 200000000000) - x) / (43188027440887 / 200000000000)) := by ring
          unfold Hcoord
          rw [hx, hy]
          exact segment_g2_23 (((-2811972559113 / 200000000000) - x) / (43188027440887 / 200000000000)) hr0 hr1
        ·
          have hxlo : x ≤ (-230) := by linarith
          rw [phi2_region_4 x hxlo]
          have hr : 0 ≤ (x / (-46) - 5) := by linarith
          have hx : (-5 * x + 4 * (-((-37 / 46) * x))) / 41 = 10 + (12 - 10) * (x / (-46) - 5) := by ring
          have hy : (4 * x + 5 * (-((-37 / 46) * x))) / 41 = (-45) + ((-54) - (-45)) * (x / (-46) - 5) := by ring
          unfold Hcoord
          rw [hx, hy]
          exact cert_tail_D (x / (-46) - 5) hr
