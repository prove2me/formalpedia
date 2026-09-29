-- Prove2me | solution 1 for VectorSpaceOpt.projection_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:48:08.457171+00:00
-- url     : https://prove2.me/submissions/95a54f94-3f8f-4fc2-a9ff-9f620b18b634

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


theorem solution {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (M : Submodule ℝ X) (x : X) (m₀ : X) (hm₀ : m₀ ∈ M) :
    ((∀ m ∈ M, ‖x - m₀‖ ≤ ‖x - m‖) ↔ (∀ m ∈ M, ⟪x - m₀, m⟫ = 0)) ∧
    (∀ m₁ ∈ M, (∀ m ∈ M, ‖x - m₁‖ ≤ ‖x - m‖) → (∀ m ∈ M, ‖x - m₀‖ ≤ ‖x - m‖) →
      m₁ = m₀) := by
  refine ⟨vsm_orth_iff_best M x m₀ hm₀, ?_⟩
  intro m₁ hm₁ h₁ h₀
  have o₁ := (vsm_orth_iff_best M x m₁ hm₁).1 h₁
  have o₀ := (vsm_orth_iff_best M x m₀ hm₀).1 h₀
  have key : ⟪m₀ - m₁, m₀ - m₁⟫ = 0 := by
    have hd : m₀ - m₁ ∈ M := M.sub_mem hm₀ hm₁
    have := o₁ _ hd
    have h2 := o₀ _ hd
    have : ⟪(x - m₁) - (x - m₀), m₀ - m₁⟫ = 0 := by
      rw [inner_sub_left, o₁ _ hd, h2]; ring
    simpa using this
  have hz : m₀ - m₁ = 0 := inner_self_eq_zero.1 key
  exact (sub_eq_zero.1 hz).symm
