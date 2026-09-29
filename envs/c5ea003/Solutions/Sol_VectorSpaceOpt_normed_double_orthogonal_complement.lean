-- Prove2me | solution 1 for VectorSpaceOpt.normed_double_orthogonal_complement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:48:39.082506+00:00
-- url     : https://prove2.me/submissions/3925ed47-6f06-40a7-bbc6-5d619b08beb3

import Mathlib

theorem vsm_eq_zero_on_of_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (M : Submodule ℝ X) (f : X →L[ℝ] ℝ) (u : ℝ) (h : ∀ m ∈ M, f m ≤ u) :
    ∀ m ∈ M, f m = 0 := by
  intro m hm
  by_contra hne
  have hb := h (((u + 1) / f m) • m) (M.smul_mem _ hm)
  rw [map_smul, smul_eq_mul] at hb
  rw [div_mul_cancel₀ _ hne] at hb
  linarith

theorem vsm_mem_of_forall_annihilator {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (M : Submodule ℝ X) (hM : IsClosed (M : Set X)) (x : X)
    (h : ∀ f : X →L[ℝ] ℝ, (∀ m ∈ M, f m = 0) → f x = 0) : x ∈ M := by
  by_contra hx
  obtain ⟨f, u, hMlt, hxgt⟩ := geometric_hahn_banach_closed_point M.convex hM hx
  have hzero : ∀ m ∈ M, f m = 0 :=
    vsm_eq_zero_on_of_le M f u (fun m hm => (hMlt m hm).le)
  have h0 : f x = 0 := h f hzero
  have hu : (0:ℝ) < u := by simpa using hMlt 0 M.zero_mem
  rw [h0] at hxgt
  linarith


theorem solution {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (M : Submodule ℝ X) (hM : IsClosed (M : Set X)) (x : X) :
    (∀ f : X →L[ℝ] ℝ, (∀ m ∈ M, f m = 0) → f x = 0) ↔ x ∈ M := by
  exact ⟨vsm_mem_of_forall_annihilator M hM x, fun hx f hf => hf x hx⟩
