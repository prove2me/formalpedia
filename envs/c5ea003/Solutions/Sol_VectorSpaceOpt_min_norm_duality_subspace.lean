-- Prove2me | solution 1 for VectorSpaceOpt.min_norm_duality_subspace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T13:01:42.164322+00:00
-- url     : https://prove2.me/submissions/886740c6-66c3-4836-ab5b-8177f27b833c

import Mathlib
import Definitions.Def_VectorSpaceOpt_aligned

section Duality
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Hahn–Banach minimum-distance duality functional for a subspace. -/
theorem vsm_exists_dual_of_subspace (M : Submodule ℝ X) (x : X) :
    ∃ f : X →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧ (∀ m ∈ M, f m = 0) ∧
      f x = Metric.infDist x (M : Set X) := by
  have hq : ∀ y : X, ‖(M.mkQ y : X ⧸ M)‖ ≤ 1 * ‖y‖ := by
    intro y; rw [one_mul]; exact Submodule.Quotient.norm_mk_le M y
  set q : X →L[ℝ] (X ⧸ M) := LinearMap.mkContinuous M.mkQ 1 hq with hqdef
  have hqn : ‖q‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  obtain ⟨g, hg1, hgx⟩ := exists_dual_vector'' ℝ (M.mkQ x)
  refine ⟨g ∘L q, ?_, ?_, ?_⟩
  · calc ‖g ∘L q‖ ≤ ‖g‖ * ‖q‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · intro m hm
    have : (M.mkQ m : X ⧸ M) = 0 := (Submodule.Quotient.mk_eq_zero M).2 hm
    simp only [ContinuousLinearMap.comp_apply, hqdef, LinearMap.mkContinuous_apply, this]
    simp
  · have hnorm : ‖(M.mkQ x : X ⧸ M)‖ = Metric.infDist x (M : Set X) :=
      QuotientAddGroup.norm_mk x
    simp only [ContinuousLinearMap.comp_apply, hqdef, LinearMap.mkContinuous_apply]
    rw [hgx, hnorm]
    norm_cast

theorem vsm_le_infDist (M : Submodule ℝ X) (x : X) (g : X →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h0 : ∀ m ∈ M, g m = 0) :
    g x ≤ Metric.infDist x (M : Set X) := by
  refine le_of_forall_lt_imp_le_of_dense ?_
  intro r hr
  by_contra hcon
  push_neg at hcon
  obtain ⟨m, hm, hmr⟩ := (Metric.infDist_lt_iff ⟨0, M.zero_mem⟩).1 hcon
  have hgx : g x = g (x - m) := by rw [map_sub, h0 m hm, sub_zero]
  have : g (x - m) ≤ ‖x - m‖ := by
    calc g (x - m) ≤ ‖g (x - m)‖ := le_abs_self _
      _ ≤ ‖g‖ * ‖x - m‖ := g.le_opNorm _
      _ ≤ 1 * ‖x - m‖ := by gcongr
      _ = ‖x - m‖ := one_mul _
  rw [← hgx] at this
  rw [dist_eq_norm] at hmr
  linarith

end Duality

theorem vsm_min_dist_duality
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (M : Submodule ℝ X) (x : X) :
    ∃ f : X →L[ℝ] ℝ,
      ‖f‖ ≤ 1 ∧
      (∀ m ∈ M, f m = 0) ∧
      f x = Metric.infDist x (M : Set X) ∧
      (∀ g : X →L[ℝ] ℝ, ‖g‖ ≤ 1 → (∀ m ∈ M, g m = 0) →
        g x ≤ Metric.infDist x (M : Set X)) ∧
      (∀ m₀ ∈ M, (∀ m ∈ M, ‖x - m₀‖ ≤ ‖x - m‖) →
        f (x - m₀) = ‖f‖ * ‖x - m₀‖) := by
  obtain ⟨f, hf1, hf0, hfx⟩ := vsm_exists_dual_of_subspace M x
  refine ⟨f, hf1, hf0, hfx, vsm_le_infDist M x, ?_⟩
  intro m₀ hm₀ hbest
  have hdist : Metric.infDist x (M : Set X) = ‖x - m₀‖ := by
    refine le_antisymm ?_ ?_
    · have : Metric.infDist x (M : Set X) ≤ dist x m₀ := Metric.infDist_le_dist_of_mem hm₀
      rwa [dist_eq_norm] at this
    · refine (Metric.le_infDist ⟨0, M.zero_mem⟩).2 ?_
      intro y hy; rw [dist_eq_norm]; exact hbest y hy
  have hfm : f (x - m₀) = ‖x - m₀‖ := by
    rw [map_sub, hf0 m₀ hm₀, sub_zero, hfx, hdist]
  rcases eq_or_lt_of_le (norm_nonneg (x - m₀)) with h0 | hpos
  · rw [hfm, ← h0, mul_zero]
  · have hge : (1:ℝ) ≤ ‖f‖ := by
      have := f.le_opNorm (x - m₀)
      rw [hfm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
      nlinarith
    have : ‖f‖ = 1 := le_antisymm hf1 hge
    rw [hfm, this, one_mul]


theorem solution {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (M : Submodule ℝ X) (x : X) :
    ∃ f₀ : X →L[ℝ] ℝ, ‖f₀‖ ≤ 1 ∧ (∀ m ∈ M, f₀ m = 0) ∧
      f₀ x = (⨅ m : M, ‖x - (m : X)‖) ∧
      (∀ f : X →L[ℝ] ℝ, ‖f‖ ≤ 1 → (∀ m ∈ M, f m = 0) →
        f x ≤ ⨅ m : M, ‖x - (m : X)‖) ∧
      (∀ m₀ ∈ M, ‖x - m₀‖ = (⨅ m : M, ‖x - (m : X)‖) →
        VectorSpaceOpt_aligned (x - m₀) f₀) := by
  have hiInf : (⨅ m : M, ‖x - (m : X)‖) = Metric.infDist x (M : Set X) := by
    rw [Metric.infDist_eq_iInf]
    exact iInf_congr fun m => (dist_eq_norm x (m : X)).symm ▸ rfl
  obtain ⟨f, hf1, hf0, hfx, hle, halign⟩ := vsm_min_dist_duality M x
  refine ⟨f, hf1, hf0, by rw [hiInf]; exact hfx, ?_, ?_⟩
  · intro g hg h0; rw [hiInf]; exact hle g hg h0
  · intro m₀ hm₀ hnorm
    refine halign m₀ hm₀ ?_
    intro m hm
    rw [hnorm, hiInf]
    have : Metric.infDist x (M : Set X) ≤ dist x m := Metric.infDist_le_dist_of_mem hm
    rwa [dist_eq_norm] at this
