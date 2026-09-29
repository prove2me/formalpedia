-- Prove2me | solution 1 for closed_unit_sublevel_gap_of_collinear_monic
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:34:21.776922+00:00
-- url     : https://prove2.me/submissions/1815a7c3-ab1f-4c3e-8b10-a1ced131e4ea

import Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_sharp_collinear_root_diameter_monic

open Polynomial Finset Set

noncomputable section

theorem solution
    {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.IsMonicOfDegree n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) :
    ∃ y : Fin n → ℝ, f = (∏ k, (X - C (base + dir * (y k : ℂ)))) ∧
      ∀ D : ℝ, IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n)
            * (D / 2) ^ n ≤ 1 →
        ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
          (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
          dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
          ∀ z ∈ segment ℝ (base + dir * (y j : ℂ))
              (base + dir * (y k : ℂ)),
            ‖f.eval z‖ ≤ 1 := by
  obtain ⟨y, hfactor, hgap⟩ :=
    ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter_monic
      hn f hf base dir hdir hcol
  refine ⟨y, hfactor, ?_⟩
  intro D hD hbudget
  obtain ⟨j, k, hjk, horder, hnoInterior, hdist, hsegment⟩ := hgap D hD
  refine ⟨j, k, hjk, horder, hnoInterior, hdist, ?_⟩
  intro z hz
  exact (hsegment z hz).trans hbudget
