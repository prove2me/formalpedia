-- Prove2me | solution 1 for VectorSpaceOpt.min_norm_linear_variety
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:48:31.712097+00:00
-- url     : https://prove2.me/submissions/bf89ab99-e64e-4387-af48-678b9f344053

import Mathlib
open scoped RealInnerProductSpace

section VSMAux
variable {Hh : Type*} [NormedAddCommGroup Hh] [InnerProductSpace ℝ Hh]

theorem vsm_best_iff_iInf (K : Set Hh) (x : Hh) {v : Hh} (hv : v ∈ K) :
    (∀ w ∈ K, ‖x - v‖ ≤ ‖x - w‖) ↔ ‖x - v‖ = ⨅ w : K, ‖x - w‖ := by
  haveI : Nonempty K := ⟨⟨v, hv⟩⟩
  have hbdd : BddBelow (Set.range fun w : K => ‖x - w‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  exact ⟨fun h => le_antisymm (le_ciInf fun w => h w w.2) (ciInf_le hbdd ⟨v, hv⟩),
    fun h w hw => h ▸ ciInf_le hbdd ⟨w, hw⟩⟩

theorem vsm_best_of_orth (M : Submodule ℝ Hh) (x v : Hh) (hv : v ∈ M)
    (h : ∀ m ∈ M, ⟪x - v, m⟫ = 0) : ∀ m ∈ M, ‖x - v‖ ≤ ‖x - m‖ := by
  intro m hm
  have hsq : ‖x - m‖ ^ 2 = ‖x - v‖ ^ 2 + ‖v - m‖ ^ 2 := by
    have hsplit : x - m = (x - v) + (v - m) := by abel
    rw [hsplit, norm_add_sq_real, h _ (M.sub_mem hv hm)]; ring
  nlinarith [norm_nonneg (x - v), norm_nonneg (x - m), sq_nonneg ‖v - m‖]

theorem vsm_orth_iff_best (M : Submodule ℝ Hh) (x v : Hh) (hv : v ∈ M) :
    (∀ m ∈ M, ‖x - v‖ ≤ ‖x - m‖) ↔ (∀ m ∈ M, ⟪x - v, m⟫ = 0) :=
  ⟨fun h => (Submodule.norm_eq_iInf_iff_real_inner_eq_zero M hv).1
      ((vsm_best_iff_iInf (M : Set Hh) x hv).1 h),
   vsm_best_of_orth M x v hv⟩

end VSMAux


theorem solution {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : Submodule ℝ H) (hM : IsClosed (M : Set H)) (x : H) :
    ∃! x₀ : H, (∃ m ∈ M, x₀ = x + m) ∧
      (∀ v : H, (∃ m ∈ M, v = x + m) → ‖x₀‖ ≤ ‖v‖) ∧
      (∀ m ∈ M, ⟪x₀, m⟫ = 0) := by
  obtain ⟨p, hp, hpinf⟩ := M.exists_norm_eq_iInf_of_complete_subspace hM.isComplete x
  have horth : ∀ m ∈ M, ⟪x - p, m⟫ = 0 :=
    (vsm_orth_iff_best M x p hp).1 ((vsm_best_iff_iInf (M : Set H) x hp).2 hpinf)
  refine ⟨x - p, ⟨⟨-p, M.neg_mem hp, by abel⟩, ?_, horth⟩, ?_⟩
  · rintro w ⟨m, hm, rfl⟩
    have hsplit : x + m = (x - p) + (p + m) := by abel
    have hsq : ‖x + m‖ ^ 2 = ‖x - p‖ ^ 2 + ‖p + m‖ ^ 2 := by
      rw [hsplit, norm_add_sq_real, horth _ (M.add_mem hp hm)]; ring
    nlinarith [norm_nonneg (x - p), norm_nonneg (x + m), sq_nonneg ‖p + m‖]
  · rintro z ⟨⟨m₁, hm₁, rfl⟩, -, hzorth⟩
    have hd : (x + m₁) - (x - p) ∈ M := by
      have : (x + m₁) - (x - p) = m₁ + p := by abel
      rw [this]; exact M.add_mem hm₁ hp
    have key : ⟪(x + m₁) - (x - p), (x + m₁) - (x - p)⟫ = (0:ℝ) := by
      rw [inner_sub_left, hzorth _ hd, horth _ hd]; ring
    have := inner_self_eq_zero.1 key
    exact sub_eq_zero.1 this
