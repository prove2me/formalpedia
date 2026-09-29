-- Prove2me | solution 1 for InnerProductGeometry.exists_mem_segment_angle_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T00:49:32.425827+00:00
-- url     : https://prove2.me/submissions/ef38d2cb-a68b-48c4-a38f-f11576e419d6

import Mathlib

open InnerProductGeometry
open scoped NNReal

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b c : V) (hb : b ≠ 0) (hc : c ≠ 0) (hpi : angle b c ≠ Real.pi)
    (θ : ℝ) (h0 : 0 ≤ θ) (hle : θ ≤ angle b c) :
    ∃ x ∈ segment ℝ b c, x ≠ 0 ∧ angle b x = θ ∧
      angle x c = angle b c - θ ∧ ‖x‖ ≤ max ‖b‖ ‖c‖ := by
  have hne : ∀ l : ℝ, l ∈ Set.Icc (0:ℝ) 1 → (1 - l) • b + l • c ≠ 0 := by
    intro l hl h
    rcases eq_or_lt_of_le hl.1 with h0' | h0'
    · rw [← h0'] at h; simp at h; exact hb h
    rcases eq_or_lt_of_le hl.2 with h1' | h1'
    · rw [h1'] at h; simp at h; exact hc h
    have hl0 : l ≠ 0 := ne_of_gt h0'
    apply hpi
    rw [angle_eq_pi_iff]
    refine ⟨hb, (l - 1) / l, div_neg_of_neg_of_pos (by linarith) h0', ?_⟩
    have h2 : l • c = -((1 - l) • b) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    have h3 := congrArg (fun v : V => l⁻¹ • v) h2
    simp only [smul_smul, inv_mul_cancel₀ hl0, one_smul, smul_neg] at h3
    rw [h3, ← neg_smul]
    congr 1
    field_simp
    ring
  set g : ℝ → ℝ := fun l => angle b ((1 - l) • b + l • c) with hgdef
  have hcont : ContinuousOn g (Set.Icc 0 1) := by
    intro l hl
    apply ContinuousAt.continuousWithinAt
    have h1 : ContinuousAt (fun y : V × V => angle y.1 y.2) (b, (1 - l) • b + l • c) :=
      continuousAt_angle hb (hne l hl)
    have h2 : ContinuousAt (fun t : ℝ => ((b : V), (1 - t) • b + t • c)) l := by fun_prop
    exact ContinuousAt.comp (g := fun y : V × V => angle y.1 y.2)
      (f := fun t : ℝ => ((b : V), (1 - t) • b + t • c)) h1 h2
  have hg0 : g 0 = 0 := by simp [hgdef, angle_self hb]
  have hg1 : g 1 = angle b c := by simp [hgdef]
  have hsub := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcont
  rw [hg0, hg1] at hsub
  obtain ⟨l, hl, hgl⟩ := hsub ⟨h0, hle⟩
  refine ⟨(1 - l) • b + l • c, ⟨1 - l, l, by linarith [hl.2], hl.1, by ring, rfl⟩,
    hne l hl, hgl, ?_, ?_⟩
  · have hmem : (1 - l) • b + l • c ∈ Submodule.span ℝ≥0 ({b, c} : Set V) := by
      rw [Submodule.mem_span_pair]
      refine ⟨⟨1 - l, by linarith [hl.2]⟩, ⟨l, hl.1⟩, ?_⟩
      simp only [NNReal.smul_def]
      rfl
    have := angle_eq_angle_add_add_angle_add_of_mem_span (hne l hl) hmem
    rw [← hgl]
    linarith [this]
  · have h1 : ‖(1 - l) • b + l • c‖ ≤ ‖(1 - l) • b‖ + ‖l • c‖ := norm_add_le _ _
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hl.2] : (0:ℝ) ≤ 1 - l), abs_of_nonneg hl.1] at h1
    have hbm : ‖b‖ ≤ max ‖b‖ ‖c‖ := le_max_left _ _
    have hcm : ‖c‖ ≤ max ‖b‖ ‖c‖ := le_max_right _ _
    nlinarith [hl.1, hl.2, norm_nonneg b, norm_nonneg c]
