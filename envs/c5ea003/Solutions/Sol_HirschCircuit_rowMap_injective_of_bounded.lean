-- Prove2me | solution 1 for HirschCircuit.rowMap_injective_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-08T18:40:38.600566+00:00
-- url     : https://prove2.me/submissions/1b9c33e6-2404-4d74-af45-878e142a81f7

import Definitions.Def_Hirsch_circuit_slack_model

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch HirschCircuit

/-- Direct proof for the published bounded row-map injectivity lemma. -/
theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hb : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b) :
    Function.Injective (rowMap a) := by
  intro p q hpq
  by_contra hpqne
  have hdiff : p - q ≠ 0 := sub_ne_zero.mpr hpqne
  have hnorm : 0 < ‖p - q‖ := norm_pos_iff.mpr hdiff
  have hker : rowMap a (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  have hline : ∀ t : ℝ, x + t • (p - q) ∈ Hpoly a b := by
    intro t i
    have hki : ⟪a i, p - q⟫ = 0 := by
      have hi := congrFun hker i
      simpa [rowMap] using hi
    have hxi := hx i
    simpa [inner_add_right, inner_smul_right, hki] using hxi
  obtain ⟨r, hr⟩ := hb.subset_closedBall x
  let t : ℝ := (r + 1) / ‖p - q‖
  have hr0 : 0 ≤ r := by
    have hball0 := Metric.mem_closedBall.mp (hr hx)
    simpa using hball0
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (by linarith) hnorm
  have hball := Metric.mem_closedBall.mp (hr (hline t))
  have hdist : dist (x + t • (p - q)) x = r + 1 := by
    rw [dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp [ne_of_gt hnorm]
  rw [hdist] at hball
  linarith

#print axioms solution
