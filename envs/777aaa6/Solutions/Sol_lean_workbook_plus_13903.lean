-- Prove2me | solution 1 for lean_workbook_plus_13903
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:34:34.374099+00:00
-- url     : https://prove2.me/submissions/85d97582-d8b5-4875-9343-eec6f60f8236

import Mathlib

namespace RationalRadicalGapRange

noncomputable def gap (x : ℝ) : ℝ :=
  2 * x / (2 * x + 1) - Real.sqrt ((2 * x - 1) / (2 * x + 1))

noncomputable def rightPoint (t : ℝ) : ℝ := (1 + t ^ 2) / (2 * (1 - t ^ 2))

noncomputable def upperInverse (z : ℝ) : ℝ := rightPoint (1 - Real.sqrt (2 * z))

noncomputable def lowerInverse (z : ℝ) : ℝ := z / (2 * (1 - z))

theorem conventional_domain {x : ℝ} (hx : 0 < x) :
    0 ≤ (2 * x - 1) / (2 * x + 1) ↔ 1 / 2 ≤ x := by
  rw [le_div_iff₀ (by linarith : 0 < 2 * x + 1)]
  constructor <;> intro h <;> linarith

theorem left_formula {x : ℝ} (hx : 0 < x) (hhalf : x ≤ 1 / 2) :
    gap x = 2 * x / (2 * x + 1) := by
  have hn : (2 * x - 1) / (2 * x + 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp [gap, Real.sqrt_eq_zero_of_nonpos hn]

theorem radical_bounds {x : ℝ} (hx : 1 / 2 ≤ x) :
    0 ≤ Real.sqrt ((2 * x - 1) / (2 * x + 1)) ∧
      Real.sqrt ((2 * x - 1) / (2 * x + 1)) < 1 := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
  apply (div_lt_iff₀ (by linarith : 0 < 2 * x + 1)).mpr
  nlinarith

theorem right_formula {x : ℝ} (hx : 1 / 2 ≤ x) :
    gap x = (1 - Real.sqrt ((2 * x - 1) / (2 * x + 1))) ^ 2 / 2 := by
  have hd : 2 * x + 1 ≠ 0 := by linarith
  have hn : 0 ≤ (2 * x - 1) / (2 * x + 1) :=
    div_nonneg (by linarith) (by linarith)
  have hs := Real.sq_sqrt hn
  have hi : 2 * (2 * x / (2 * x + 1)) = 1 + (2 * x - 1) / (2 * x + 1) := by
    field_simp
    ring
  unfold gap
  nlinarith only [hs, hi]

theorem right_point {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    1 / 2 ≤ rightPoint t ∧
      Real.sqrt ((2 * rightPoint t - 1) / (2 * rightPoint t + 1)) = t ∧
      gap (rightPoint t) = (1 - t) ^ 2 / 2 := by
  have ht2 : t ^ 2 < 1 := by nlinarith
  have hd : 0 < 2 * (1 - t ^ 2) := by linarith
  have hp : 1 / 2 ≤ rightPoint t := by
    unfold rightPoint
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg t]
  have he : (2 * rightPoint t - 1) / (2 * rightPoint t + 1) = t ^ 2 := by
    apply (div_eq_iff (show 2 * rightPoint t + 1 ≠ 0 by linarith)).mpr
    unfold rightPoint
    field_simp [show 1 - t ^ 2 ≠ 0 by linarith]
    ring
  have hs : Real.sqrt ((2 * rightPoint t - 1) / (2 * rightPoint t + 1)) = t := by
    rw [he, Real.sqrt_sq ht]
  exact ⟨hp, hs, by rw [right_formula hp, hs]⟩

theorem right_reconstruction {x : ℝ} (hx : 1 / 2 ≤ x) :
    rightPoint (Real.sqrt ((2 * x - 1) / (2 * x + 1))) = x := by
  have hn : 0 ≤ (2 * x - 1) / (2 * x + 1) :=
    div_nonneg (by linarith) (by linarith)
  have hd : 2 * x + 1 ≠ 0 := by linarith
  unfold rightPoint
  rw [Real.sq_sqrt hn]
  field_simp
  ring

theorem positive_bounds {x : ℝ} (hx : 0 < x) : 0 < gap x ∧ gap x ≤ 1 / 2 := by
  rcases le_total x (1 / 2) with h | h
  · rw [left_formula hx h]
    exact ⟨div_pos (by linarith) (by linarith),
      (div_le_iff₀ (by linarith : 0 < 2 * x + 1)).mpr (by linarith)⟩
  · rw [right_formula h]
    obtain ⟨ht, ht1⟩ := radical_bounds h
    constructor
    · exact div_pos (sq_pos_of_pos (by linarith)) (by norm_num)
    · nlinarith

theorem source_strict {x : ℝ} (hx : 1 / 2 ≤ x) :
    Real.sqrt ((2 * x - 1) / (2 * x + 1)) < 2 * x / (2 * x + 1) := by
  have h := (positive_bounds (show 0 < x by linarith)).1
  exact sub_pos.mp h

theorem maximum_iff {x : ℝ} (hx : 0 < x) : gap x = 1 / 2 ↔ x = 1 / 2 := by
  constructor
  · intro he
    rcases le_total x (1 / 2) with h | h
    · rw [left_formula hx h] at he
      have hm := (div_eq_iff (show 2 * x + 1 ≠ 0 by linarith)).mp he
      linarith
    · have hr := right_formula h
      obtain ⟨ht, ht1⟩ := radical_bounds h
      have hz : Real.sqrt ((2 * x - 1) / (2 * x + 1)) = 0 := by nlinarith
      have hn : 0 ≤ (2 * x - 1) / (2 * x + 1) :=
        div_nonneg (by linarith) (by linarith)
      have hs := Real.sq_sqrt hn
      rw [hz] at hs
      have hzero : 2 * x - 1 = 0 :=
        (div_eq_zero_iff.mp (by nlinarith : (2 * x - 1) / (2 * x + 1) = 0)).resolve_right
          (by linarith)
      linarith
  · rintro rfl
    norm_num [gap]

theorem upper_inverse {z : ℝ} (hz : 0 < z) (hzhalf : z ≤ 1 / 2) :
    1 / 2 ≤ upperInverse z ∧ gap (upperInverse z) = z := by
  have hs : 0 < Real.sqrt (2 * z) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : Real.sqrt (2 * z) ≤ 1 :=
    (Real.sqrt_le_one).mpr (by linarith)
  obtain ⟨hp, _, hg⟩ := right_point (show 0 ≤ 1 - Real.sqrt (2 * z) by linarith)
    (show 1 - Real.sqrt (2 * z) < 1 by linarith)
  have hs2 := Real.sq_sqrt (show 0 ≤ 2 * z by linarith)
  exact ⟨hp, by unfold upperInverse; rw [hg]; nlinarith only [hs2]⟩

theorem upper_fiber {z x : ℝ} (hz : 0 < z) (hzhalf : z ≤ 1 / 2) :
    (1 / 2 ≤ x ∧ gap x = z) ↔ x = upperInverse z := by
  constructor
  · rintro ⟨hx, hg⟩
    obtain ⟨ht, ht1⟩ := radical_bounds hx
    have hf := right_formula hx
    have hs := Real.sq_sqrt (show 0 ≤ 2 * z by linarith)
    have hsz := Real.sqrt_nonneg (2 * z)
    have he : Real.sqrt ((2 * x - 1) / (2 * x + 1)) = 1 - Real.sqrt (2 * z) := by
      nlinarith
    rw [← right_reconstruction hx, he]
    rfl
  · rintro rfl
    exact upper_inverse hz hzhalf

theorem lower_inverse {z : ℝ} (hz : 0 < z) (hzhalf : z ≤ 1 / 2) :
    0 < lowerInverse z ∧ lowerInverse z ≤ 1 / 2 ∧ gap (lowerInverse z) = z := by
  have hd : 0 < 2 * (1 - z) := by linarith
  have hp : 0 < lowerInverse z := div_pos hz hd
  have hh : lowerInverse z ≤ 1 / 2 := by
    unfold lowerInverse
    apply (div_le_iff₀ hd).mpr
    linarith
  refine ⟨hp, hh, ?_⟩
  rw [left_formula hp hh]
  apply (div_eq_iff (show 2 * lowerInverse z + 1 ≠ 0 by linarith)).mpr
  unfold lowerInverse
  field_simp [show 1 - z ≠ 0 by linarith]
  ring

theorem lower_fiber {z x : ℝ} (hz : 0 < z) (hzhalf : z ≤ 1 / 2) :
    (0 < x ∧ x ≤ 1 / 2 ∧ gap x = z) ↔ x = lowerInverse z := by
  constructor
  · rintro ⟨hx, hh, hg⟩
    rw [left_formula hx hh] at hg
    have he := (div_eq_iff (show 2 * x + 1 ≠ 0 by linarith)).mp hg
    unfold lowerInverse
    apply (eq_div_iff (show 2 * (1 - z) ≠ 0 by linarith)).mpr
    nlinarith only [he]
  · rintro rfl
    exact lower_inverse hz hzhalf

theorem positive_fiber {z x : ℝ} (hz : 0 < z) (hzhalf : z ≤ 1 / 2) :
    (0 < x ∧ gap x = z) ↔ x = lowerInverse z ∨ x = upperInverse z := by
  constructor
  · rintro ⟨hx, hg⟩
    rcases le_total x (1 / 2) with hh | hh
    · exact Or.inl ((lower_fiber hz hzhalf).mp ⟨hx, hh, hg⟩)
    · exact Or.inr ((upper_fiber hz hzhalf).mp ⟨hh, hg⟩)
  · rintro (rfl | rfl)
    · have h := lower_inverse hz hzhalf
      exact ⟨h.1, h.2.2⟩
    · have h := upper_inverse hz hzhalf
      exact ⟨by linarith [h.1], h.2⟩

theorem conventional_range :
    {z : ℝ | ∃ x : ℝ, 1 / 2 ≤ x ∧ gap x = z} = Set.Ioc 0 (1 / 2) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact positive_bounds (by linarith)
  · intro hz
    exact ⟨upperInverse z, upper_inverse hz.1 hz.2⟩

theorem positive_range :
    {z : ℝ | ∃ x : ℝ, 0 < x ∧ gap x = z} = Set.Ioc 0 (1 / 2) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact positive_bounds hx
  · intro hz
    have h := upper_inverse hz.1 hz.2
    exact ⟨upperInverse z, by linarith [h.1], h.2⟩

theorem conventional_unique {z : ℝ} (hz : 0 < z) (hzhalf : z ≤ 1 / 2) :
    ∃! x : ℝ, 1 / 2 ≤ x ∧ gap x = z := by
  refine ⟨upperInverse z, upper_inverse hz hzhalf, ?_⟩
  intro x hx
  exact (upper_fiber hz hzhalf).mp hx

theorem two_positive_preimages {z : ℝ} (hz : 0 < z) (hzhalf : z < 1 / 2) :
    lowerInverse z < 1 / 2 ∧ 1 / 2 < upperInverse z ∧
      ∀ x : ℝ, (0 < x ∧ gap x = z) ↔
        x = lowerInverse z ∨ x = upperInverse z := by
  have hl := lower_inverse hz hzhalf.le
  have hu := upper_inverse hz hzhalf.le
  have hlne : lowerInverse z ≠ 1 / 2 := by
    intro he
    have hv := (maximum_iff hl.1).mpr he
    linarith [hl.2.2]
  have hune : upperInverse z ≠ 1 / 2 := by
    intro he
    have hv := (maximum_iff (show 0 < upperInverse z by linarith [hu.1])).mpr he
    linarith [hu.2]
  exact ⟨lt_of_le_of_ne hl.2.1 hlne, lt_of_le_of_ne hu.1 (Ne.symm hune),
    fun _ => positive_fiber hz hzhalf.le⟩

end RationalRadicalGapRange

theorem solution (x : ℝ) (hx : 0 < x) :
    2 * x / (2 * x + 1) > Real.sqrt ((2 * x - 1) / (2 * x + 1)) :=
  sub_pos.mp (RationalRadicalGapRange.positive_bounds hx).1

#print axioms RationalRadicalGapRange.gap
#print axioms RationalRadicalGapRange.rightPoint
#print axioms RationalRadicalGapRange.upperInverse
#print axioms RationalRadicalGapRange.lowerInverse
#print axioms RationalRadicalGapRange.conventional_domain
#print axioms RationalRadicalGapRange.left_formula
#print axioms RationalRadicalGapRange.radical_bounds
#print axioms RationalRadicalGapRange.right_formula
#print axioms RationalRadicalGapRange.right_point
#print axioms RationalRadicalGapRange.right_reconstruction
#print axioms RationalRadicalGapRange.positive_bounds
#print axioms RationalRadicalGapRange.source_strict
#print axioms RationalRadicalGapRange.maximum_iff
#print axioms RationalRadicalGapRange.upper_inverse
#print axioms RationalRadicalGapRange.upper_fiber
#print axioms RationalRadicalGapRange.lower_inverse
#print axioms RationalRadicalGapRange.lower_fiber
#print axioms RationalRadicalGapRange.positive_fiber
#print axioms RationalRadicalGapRange.conventional_range
#print axioms RationalRadicalGapRange.positive_range
#print axioms RationalRadicalGapRange.conventional_unique
#print axioms RationalRadicalGapRange.two_positive_preimages
#print axioms solution
