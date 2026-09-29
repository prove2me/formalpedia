-- Prove2me | solution 1 for VectorSpaceOpt.fourier_best_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:48:14.260804+00:00
-- url     : https://prove2.me/submissions/209a5503-08c8-4de6-9a2f-8ad77435252d

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
    [InnerProductSpace ℝ H] {n : ℕ} (e : Fin n → H) (he : Orthonormal ℝ e) (x : H) :
    ∀ m ∈ Submodule.span ℝ (Set.range e),
      ‖x - ∑ i, ⟪x, e i⟫ • e i‖ ≤ ‖x - m‖ := by
  set v : H := ∑ i, ⟪x, e i⟫ • e i with hvdef
  have hv : v ∈ Submodule.span ℝ (Set.range e) :=
    Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine vsm_best_of_orth _ x v hv ?_
  have hgen : ∀ j : Fin n, ⟪x - v, e j⟫ = 0 := by
    intro j
    have : ⟪v, e j⟫ = ⟪x, e j⟫ := by
      rw [hvdef, sum_inner]
      rw [Finset.sum_eq_single j]
      · rw [real_inner_smul_left, inner_self_eq_one_of_norm_eq_one (he.1 j), mul_one]
      · intro b _ hb
        rw [real_inner_smul_left, he.2 hb]; ring
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [inner_sub_left, this]; ring
  intro m hm
  induction hm using Submodule.span_induction with
  | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hgen j
  | zero => simp
  | add a b _ _ ha hb => rw [inner_add_right, ha, hb]; ring
  | smul c a _ ha => rw [real_inner_smul_right, ha]; ring
