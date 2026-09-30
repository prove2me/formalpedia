-- Prove2me | solution 1 for lean_workbook_plus_28069
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:53:06.158709+00:00
-- url     : https://prove2.me/submissions/1f127daa-bcc1-4591-a1d8-4786fa8a5706

import Mathlib

namespace ShiftedReciprocalExactRange

noncomputable def value (r : ℝ) : ℝ := 8 * r + 9 * (1 - r) / (1 + r)

noncomputable def inversePoint (v : ℝ) : ℝ :=
  (v + 1 + Real.sqrt ((v - 7) * (v + 41))) / 16

theorem gap_identities (r : ℝ) (hr : r ≠ -1) :
    (1 + r) * (value r - 7) = 2 * (2 * r - 1) ^ 2 ∧
      (1 + r) * (value r + 41) = 2 * (2 * r + 5) ^ 2 := by
  have hd : 1 + r ≠ 0 := by
    intro hz
    apply hr
    linarith only [hz]
  constructor <;> unfold value <;> field_simp [hd] <;> ring

theorem genuine_models : value (1 / 2) = 7 ∧ value (-5 / 2) = -41 ∧ value (-1) = -8 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold value
    ring
  · unfold value
    ring
  · norm_num [value]

theorem positive_branch_bound (r : ℝ) (hr : -1 < r) : 7 ≤ value r := by
  have hg := (gap_identities r (ne_of_gt hr)).1
  have hm : 0 ≤ (1 + r) * (value r - 7) := by rw [hg]; positivity
  rcases mul_nonneg_iff.mp hm with h | h
  · linarith only [h.2]
  · linarith only [h.1, hr]

theorem negative_branch_bound (r : ℝ) (hr : r < -1) : value r ≤ -41 := by
  have hg := (gap_identities r (ne_of_lt hr)).2
  have hm : 0 ≤ (1 + r) * (value r + 41) := by rw [hg]; positivity
  rcases mul_nonneg_iff.mp hm with h | h
  · linarith only [h.1, hr]
  · linarith only [h.2]

theorem positive_branch_equality (r : ℝ) (hr : -1 < r) :
    value r = 7 ↔ r = 1 / 2 := by
  constructor
  · intro he
    have hg := (gap_identities r (ne_of_gt hr)).1
    rw [he] at hg
    have hz : (2 * r - 1) ^ 2 = 0 := by nlinarith only [hg]
    have hs := sq_eq_zero_iff.mp hz
    linarith only [hs]
  · rintro rfl
    exact genuine_models.1

theorem negative_branch_equality (r : ℝ) (hr : r < -1) :
    value r = -41 ↔ r = -5 / 2 := by
  constructor
  · intro he
    have hg := (gap_identities r (ne_of_lt hr)).2
    rw [he] at hg
    have hz : (2 * r + 5) ^ 2 = 0 := by nlinarith only [hg]
    have hs := sq_eq_zero_iff.mp hz
    linarith only [hs]
  · rintro rfl
    exact genuine_models.2.1

theorem level_equation (r v : ℝ) (hr : r ≠ -1) :
    value r = v ↔ 8 * r ^ 2 - (v + 1) * r + (9 - v) = 0 := by
  have hd : 1 + r ≠ 0 := by
    intro hz
    apply hr
    linarith only [hz]
  unfold value
  constructor
  · intro h
    field_simp [hd] at h
    nlinarith only [h]
  · intro h
    field_simp [hd]
    nlinarith only [h]

theorem discriminant_nonneg (r : ℝ) (hr : r ≠ -1) :
    0 ≤ (value r - 7) * (value r + 41) := by
  have hl := (level_equation r (value r) hr).mp rfl
  have hi : (16 * r - (value r + 1)) ^ 2 = (value r - 7) * (value r + 41) := by
    linear_combination 32 * hl
  rw [← hi]
  exact sq_nonneg _

theorem inverse_model (v : ℝ) (hv : 0 ≤ (v - 7) * (v + 41)) :
    inversePoint v ≠ -1 ∧ value (inversePoint v) = v := by
  have hs := Real.sq_sqrt hv
  have hn : inversePoint v ≠ -1 := by
    intro he
    unfold inversePoint at he
    have hroot : Real.sqrt ((v - 7) * (v + 41)) = -v - 17 := by linarith only [he]
    rw [hroot] at hs
    nlinarith only [hs]
  refine ⟨hn, (level_equation (inversePoint v) v hn).mpr ?_⟩
  unfold inversePoint
  nlinarith only [hs]

theorem exact_range : Set.range value = {v : ℝ | v ≤ -41 ∨ v = -8 ∨ 7 ≤ v} := by
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    by_cases hr : r = -1
    · subst r
      exact Or.inr (Or.inl genuine_models.2.2)
    · have hd := discriminant_nonneg r hr
      rcases mul_nonneg_iff.mp hd with h | h
      · exact Or.inr (Or.inr (by linarith only [h.1]))
      · exact Or.inl (by linarith only [h.2])
  · rintro (hv | hv | hv)
    · have hd : 0 ≤ (v - 7) * (v + 41) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      exact ⟨inversePoint v, (inverse_model v hd).2⟩
    · exact ⟨-1, hv.symm ▸ genuine_models.2.2⟩
    · have hd : 0 ≤ (v - 7) * (v + 41) := mul_nonneg (by linarith) (by linarith)
      exact ⟨inversePoint v, (inverse_model v hd).2⟩

theorem positive_branch_minimum : IsLeast {v : ℝ | ∃ r : ℝ, -1 < r ∧ value r = v} 7 := by
  refine ⟨⟨1 / 2, by norm_num, genuine_models.1⟩, ?_⟩
  rintro v ⟨r, hr, rfl⟩
  exact positive_branch_bound r hr

theorem unit_interval_minimum :
    IsLeast {v : ℝ | ∃ r ∈ Set.Icc (0 : ℝ) 1, value r = v} 7 := by
  refine ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, genuine_models.1⟩, ?_⟩
  rintro v ⟨r, hr, rfl⟩
  exact positive_branch_bound r (by linarith only [hr.1])

theorem negative_branch_maximum : IsGreatest {v : ℝ | ∃ r : ℝ, r < -1 ∧ value r = v} (-41) := by
  refine ⟨⟨-5 / 2, by norm_num, genuine_models.2.1⟩, ?_⟩
  rintro v ⟨r, hr, rfl⟩
  exact negative_branch_bound r hr

theorem unbounded_below (M : ℝ) : ∃ r : ℝ, value r < M := by
  have hv : min (-41) (M - 1) ∈ Set.range value := by
    rw [exact_range]
    exact Or.inl (min_le_left _ _)
  obtain ⟨r, hr⟩ := hv
  refine ⟨r, ?_⟩
  rw [hr]
  exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

theorem unbounded_above (M : ℝ) : ∃ r : ℝ, M < value r := by
  have hv : max 7 (M + 1) ∈ Set.range value := by
    rw [exact_range]
    exact Or.inr (Or.inr (le_max_left _ _))
  obtain ⟨r, hr⟩ := hv
  refine ⟨r, ?_⟩
  rw [hr]
  exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

theorem no_global_minimum : ¬ ∃ r : ℝ, ∀ s : ℝ, value r ≤ value s := by
  rintro ⟨r, h⟩
  obtain ⟨s, hs⟩ := unbounded_below (value r)
  exact (not_lt_of_ge (h s)) hs

end ShiftedReciprocalExactRange

theorem solution (f : ℝ → ℝ) (r_1 : ℝ)
    (hf : f r_1 = 8 * r_1 + 9 * (1 - r_1) / (1 + r_1)) :
    ∃ r_1_min, f r_1_min ≤ f r_1 := by
  exact ⟨r_1, le_rfl⟩

#print axioms ShiftedReciprocalExactRange.gap_identities
#print axioms ShiftedReciprocalExactRange.genuine_models
#print axioms ShiftedReciprocalExactRange.positive_branch_bound
#print axioms ShiftedReciprocalExactRange.negative_branch_bound
#print axioms ShiftedReciprocalExactRange.positive_branch_equality
#print axioms ShiftedReciprocalExactRange.negative_branch_equality
#print axioms ShiftedReciprocalExactRange.level_equation
#print axioms ShiftedReciprocalExactRange.discriminant_nonneg
#print axioms ShiftedReciprocalExactRange.inverse_model
#print axioms ShiftedReciprocalExactRange.exact_range
#print axioms ShiftedReciprocalExactRange.positive_branch_minimum
#print axioms ShiftedReciprocalExactRange.unit_interval_minimum
#print axioms ShiftedReciprocalExactRange.negative_branch_maximum
#print axioms ShiftedReciprocalExactRange.unbounded_below
#print axioms ShiftedReciprocalExactRange.unbounded_above
#print axioms ShiftedReciprocalExactRange.no_global_minimum
#print axioms solution
