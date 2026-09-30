-- Prove2me | solution 1 for lean_workbook_plus_25787
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:30:18.875998+00:00
-- url     : https://prove2.me/submissions/9cba6315-0e43-438b-97e7-d92cff7725ba

import Mathlib

namespace ReciprocalProductSharpBound

noncomputable def value (a b : ℝ) : ℝ := 1 / (2 * a) + 1 / (b + 1) + 1 / (a * b + b)

noncomputable def ratio (a b : ℝ) : ℝ := (a * b + 1) * value a b

def denominator (a b : ℝ) : ℝ := 2 * a * b * (a + 1) * (b + 1)

theorem denominator_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < denominator a b := by
  unfold denominator
  positivity

theorem gap_identity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    denominator a b * (ratio a b - 3) =
      b ^ 2 * (a + 1) * (a - 1) ^ 2 + a * (b + 1) * (b - 1) ^ 2 +
        (a + b) * (a * b - 1) ^ 2 := by
  have h1 : b + 1 ≠ 0 := by positivity
  have h2 : a * b + b ≠ 0 := by positivity
  unfold denominator ratio value
  field_simp
  ring

theorem ratio_lower_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 3 ≤ ratio a b := by
  have hn : 0 ≤ denominator a b * (ratio a b - 3) := by
    rw [gap_identity ha hb]
    positivity
  have hd := denominator_pos ha hb
  nlinarith only [hn, hd]

theorem source_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    3 / (a * b + 1) ≤ value a b := by
  apply (div_le_iff₀ (by positivity : 0 < a * b + 1)).mpr
  simpa only [ratio, mul_comm] using ratio_lower_bound ha hb

theorem ratio_equality {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ratio a b = 3 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro he
    have hg := gap_identity ha hb
    rw [he, sub_self, mul_zero] at hg
    have h1 : 0 ≤ b ^ 2 * (a + 1) * (a - 1) ^ 2 := by positivity
    have h2 : 0 ≤ a * (b + 1) * (b - 1) ^ 2 := by positivity
    have h3 : 0 ≤ (a + b) * (a * b - 1) ^ 2 := by positivity
    have he1 : b ^ 2 * (a + 1) * (a - 1) ^ 2 = 0 := by
      linarith only [hg, h1, h2, h3]
    have he2 : a * (b + 1) * (b - 1) ^ 2 = 0 := by
      linarith only [hg, h1, h2, h3]
    have hs1 := (mul_eq_zero.mp he1).resolve_left
      (ne_of_gt (by positivity : 0 < b ^ 2 * (a + 1)))
    have hs2 := (mul_eq_zero.mp he2).resolve_left
      (ne_of_gt (by positivity : 0 < a * (b + 1)))
    constructor <;> nlinarith only [hs1, hs2]
  · rintro ⟨rfl, rfl⟩
    norm_num [ratio, value]
    rfl

theorem source_equality {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    value a b = 3 / (a * b + 1) ↔ a = 1 ∧ b = 1 := by
  have hd : a * b + 1 ≠ 0 := by positivity
  rw [← ratio_equality ha hb, eq_div_iff hd]
  simp only [ratio, mul_comm]

theorem slice_formula {a : ℝ} (ha : 0 < a) :
    ratio a 1 = (a ^ 2 + 4 * a + 1) / (2 * a) := by
  have hap : a + 1 ≠ 0 := by positivity
  unfold ratio value
  field_simp
  ring

theorem slice_attains {z : ℝ} (hz : 3 ≤ z) :
    ∃ a : ℝ, 0 < a ∧ ratio a 1 = z := by
  let r := Real.sqrt ((z - 2) ^ 2 - 1)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hd : 0 ≤ (z - 2) ^ 2 - 1 := by nlinarith only [hz]
  have hr2 : r ^ 2 = (z - 2) ^ 2 - 1 := Real.sq_sqrt hd
  let a := z - 2 + r
  have ha : 0 < a := by dsimp [a]; linarith only [hz, hr]
  have hq : a ^ 2 - 2 * (z - 2) * a + 1 = 0 := by
    dsimp [a]
    nlinarith only [hr2]
  refine ⟨a, ha, ?_⟩
  rw [slice_formula ha]
  apply (div_eq_iff (by positivity : (2 : ℝ) * a ≠ 0)).mpr
  nlinarith only [hq]

theorem attained_range :
    {z : ℝ | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ratio a b = z} = Set.Ici 3 := by
  ext z
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ratio_lower_bound ha hb
  · intro hz
    obtain ⟨a, ha, he⟩ := slice_attains hz
    exact ⟨a, 1, ha, by norm_num, he⟩

theorem least_ratio : IsLeast
    {z : ℝ | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ratio a b = z} 3 := by
  rw [attained_range]
  exact ⟨by simp, fun _ h => h⟩

theorem sharp_coefficient (k : ℝ) :
    (∀ a b : ℝ, 0 < a → 0 < b → k / (a * b + 1) ≤ value a b) ↔ k ≤ 3 := by
  constructor
  · intro h
    have he := h 1 1 (by norm_num) (by norm_num)
    norm_num [value] at he
    linarith
  · intro hk a b ha hb
    exact (div_le_div_of_nonneg_right hk (by positivity)).trans (source_bound ha hb)

end ReciprocalProductSharpBound

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / (2 * a) + 1 / (b + 1) + 1 / (a * b + b) ≥ 3 / (a * b + 1) :=
  ReciprocalProductSharpBound.source_bound ha hb

#print axioms ReciprocalProductSharpBound.value
#print axioms ReciprocalProductSharpBound.ratio
#print axioms ReciprocalProductSharpBound.denominator
#print axioms ReciprocalProductSharpBound.denominator_pos
#print axioms ReciprocalProductSharpBound.gap_identity
#print axioms ReciprocalProductSharpBound.ratio_lower_bound
#print axioms ReciprocalProductSharpBound.source_bound
#print axioms ReciprocalProductSharpBound.ratio_equality
#print axioms ReciprocalProductSharpBound.source_equality
#print axioms ReciprocalProductSharpBound.slice_formula
#print axioms ReciprocalProductSharpBound.slice_attains
#print axioms ReciprocalProductSharpBound.attained_range
#print axioms ReciprocalProductSharpBound.least_ratio
#print axioms ReciprocalProductSharpBound.sharp_coefficient
#print axioms solution
