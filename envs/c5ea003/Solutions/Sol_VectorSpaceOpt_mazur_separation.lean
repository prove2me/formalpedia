-- Prove2me | solution 1 for VectorSpaceOpt.mazur_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:48:46.466029+00:00
-- url     : https://prove2.me/submissions/8fb2d483-086c-4536-a6c5-805a25a0d872

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


theorem solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (M : Submodule ℝ X) (x₀ : X)
    (hdisj : ∀ m ∈ M, x₀ + m ∉ interior K) :
    ∃ (f : X →L[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ m ∈ M, f (x₀ + m) = c) ∧
      (∀ k ∈ interior K, f k < c) ∧ (∀ k ∈ K, f k ≤ c) := by
  classical
  set V : Set X := (fun m => x₀ + m) '' (M : Set X) with hVdef
  have hVconv : Convex ℝ V := M.convex.translate x₀
  have hdis : Disjoint (interior K) V := by
    rw [Set.disjoint_left]
    rintro a ha ⟨m, hm, rfl⟩
    exact hdisj m hm ha
  obtain ⟨f, u, hfA, hfB⟩ :=
    geometric_hahn_banach_open hK.interior isOpen_interior hVconv hdis
  -- `f` is bounded below on the translate, hence vanishes on `M`
  have hMzero : ∀ m ∈ M, f m = 0 := by
    have hle : ∀ m ∈ M, (-f) m ≤ f x₀ - u := by
      intro m hm
      have := hfB (x₀ + m) ⟨m, hm, rfl⟩
      rw [map_add] at this
      simp only [ContinuousLinearMap.neg_apply]
      linarith
    intro m hm
    have := vsm_eq_zero_on_of_le M (-f) (f x₀ - u) hle m hm
    simpa using this
  refine ⟨f, f x₀, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    obtain ⟨a, ha⟩ := hKi
    have h1 : (0:ℝ) < u := by simpa using hfA a ha
    have h2 : u ≤ (0:ℝ) := by simpa using hfB x₀ ⟨0, M.zero_mem, by simp⟩
    linarith
  · intro m hm; rw [map_add, hMzero m hm, add_zero]
  · intro k hk
    have h1 : f k < u := hfA k hk
    have h2 : u ≤ f x₀ := by simpa using hfB x₀ ⟨0, M.zero_mem, by simp⟩
    linarith
  · intro k hk
    have hKsub : K ⊆ closure (interior K) := by
      rw [hK.closure_interior_eq_closure_of_nonempty_interior hKi]; exact subset_closure
    have hsub : K ⊆ f ⁻¹' (Set.Iic u) :=
      hKsub.trans (closure_minimal (fun y hy => (hfA y hy).le)
        (isClosed_Iic.preimage f.continuous))
    have h1 : f k ≤ u := hsub hk
    have h2 : u ≤ f x₀ := by simpa using hfB x₀ ⟨0, M.zero_mem, by simp⟩
    linarith
