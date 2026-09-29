-- Prove2me | solution 1 for bousquet_cgf_le_phi_via_herbst
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-24T02:24:00.834+00:00
-- url     : https://prove2.me/submissions/0f79e1c2-830e-4b76-a809-ea687b3c6b26

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

open Set Real

theorem solution
    (G G' G'' : ℝ → ℝ) (v L : ℝ) (hL : 0 ≤ L) (hv : 0 ≤ v)
    (hG0 : G 0 = 0) (hG'0 : G' 0 = 0)
    (hG_cont : ContinuousOn G (Icc 0 L))
    (hG'_cont : ContinuousOn G' (Icc 0 L))
    (hG_deriv : ∀ x ∈ Ico (0:ℝ) L, HasDerivWithinAt G (G' x) (Ici x) x)
    (hG'_deriv : ∀ x ∈ Ico (0:ℝ) L, HasDerivWithinAt G' (G'' x) (Ici x) x)
    (hG''_bound : ∀ x ∈ Ico (0:ℝ) L, G'' x ≤ v * Real.exp x) :
    G L ≤ v * (Real.exp L - 1 - L) := by
  -- Step 1: integrate G'' ≤ v e^x with G' 0 = 0 ⟹ G' x ≤ v (e^x − 1) on [0,L].
  -- Boundary B1 x = v (e^x − 1); B1 0 = 0 = G' 0; B1' x = v e^x ≥ G'' x.
  have hstep1 : ∀ x ∈ Icc (0:ℝ) L, G' x ≤ v * (Real.exp x - 1) := by
    set B1 : ℝ → ℝ := fun x => v * (Real.exp x - 1) with hB1
    have hB1_cont : ContinuousOn B1 (Icc 0 L) := by
      apply Continuous.continuousOn; fun_prop
    have hB1_deriv : ∀ x ∈ Ico (0:ℝ) L, HasDerivWithinAt B1 (v * Real.exp x) (Ici x) x := by
      intro x _
      have h := (Real.hasDerivAt_exp x).hasDerivWithinAt (s := Ici x)
      have h2 : HasDerivWithinAt (fun x => Real.exp x - 1) (Real.exp x) (Ici x) x := by
        simpa using h.sub_const 1
      simpa [hB1, mul_comm] using h2.const_mul v
    have hbase : G' 0 ≤ B1 0 := by simp [hB1, hG'0]
    intro x hx
    exact image_le_of_deriv_right_le_deriv_boundary hG'_cont hG'_deriv hbase
      hB1_cont hB1_deriv hG''_bound hx
  -- Step 2: integrate G' ≤ v (e^x − 1) with G 0 = 0 ⟹ G x ≤ v (e^x − 1 − x) on [0,L].
  -- Boundary B2 x = v (e^x − 1 − x); B2 0 = 0 = G 0; B2' x = v (e^x − 1) ≥ G' x.
  set B2 : ℝ → ℝ := fun x => v * (Real.exp x - 1 - x) with hB2
  have hB2_cont : ContinuousOn B2 (Icc 0 L) := by
    apply Continuous.continuousOn; fun_prop
  have hB2_deriv : ∀ x ∈ Ico (0:ℝ) L, HasDerivWithinAt B2 (v * (Real.exp x - 1)) (Ici x) x := by
    intro x _
    have h := (Real.hasDerivAt_exp x).hasDerivWithinAt (s := Ici x)
    have h2 : HasDerivWithinAt (fun x => Real.exp x - 1 - x) (Real.exp x - 1) (Ici x) x := by
      have := (h.sub_const 1).sub (hasDerivWithinAt_id x (Ici x))
      simpa using this
    simpa [hB2, mul_comm] using h2.const_mul v
  have hbase2 : G 0 ≤ B2 0 := by simp [hB2, hG0]
  have hbound2 : ∀ x ∈ Ico (0:ℝ) L, G' x ≤ v * (Real.exp x - 1) := by
    intro x hx; exact hstep1 x (Ico_subset_Icc_self hx)
  have hfinal : G L ≤ B2 L :=
    image_le_of_deriv_right_le_deriv_boundary hG_cont hG_deriv hbase2 hB2_cont hB2_deriv
      hbound2 (right_mem_Icc.mpr hL)
  simpa [hB2] using hfinal

