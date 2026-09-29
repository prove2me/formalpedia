-- Prove2me | solution 1 for VectorSpaceOpt.normal_equations
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:48:29.336294+00:00
-- url     : https://prove2.me/submissions/b44d78ae-84ef-466b-855d-509f67a703eb

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


theorem solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (y : Fin n → H) (x : H) (α : Fin n → ℝ) :
    (∀ i, ∑ j, ⟪y j, y i⟫ * α j = ⟪x, y i⟫) ↔
    (∀ m ∈ Submodule.span ℝ (Set.range y), ‖x - ∑ j, α j • y j‖ ≤ ‖x - m‖) := by
  set M := Submodule.span ℝ (Set.range y) with hM
  set v : H := ∑ j, α j • y j with hv
  have hvmem : v ∈ M :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [vsm_orth_iff_best M x v hvmem]
  constructor
  · intro hgen m hm
    have hbase : ∀ i, ⟪x - v, y i⟫ = 0 := by
      intro i
      have : ⟪v, y i⟫ = ⟪x, y i⟫ := by
        rw [hv, sum_inner]
        simpa [real_inner_smul_left, mul_comm] using hgen i
      rw [inner_sub_left, this]; ring
    induction hm using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hbase i
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb]; ring
    | smul c a _ ha => rw [real_inner_smul_right, ha]; ring
  · intro h i
    have hyi : y i ∈ M := Submodule.subset_span ⟨i, rfl⟩
    have := h _ hyi
    rw [inner_sub_left] at this
    have hvi : ⟪v, y i⟫ = ∑ j, ⟪y j, y i⟫ * α j := by
      rw [hv, sum_inner]
      exact Finset.sum_congr rfl fun j _ => by rw [real_inner_smul_left]; ring
    rw [hvi] at this
    linarith
