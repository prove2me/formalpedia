-- Prove2me | solution 1 for lean_workbook_plus_28289
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:42:30.401177+00:00
-- url     : https://prove2.me/submissions/0f953cf1-8481-4e85-9db5-c49049ac2dc9

import Mathlib

namespace RefinedAMGMSharpCoefficient

noncomputable def value (a b c : ℝ) : ℝ := (b + c) / a + a ^ 2 / (b * c)

noncomputable def correction (a b c : ℝ) : ℝ := (c - a) ^ 2 / (c * (a + b))

noncomputable def ratio (a b c : ℝ) : ℝ := (value a b c - 3) / correction a b c

def denominator (a b c : ℝ) : ℝ := a * b * c * (a + b)

theorem denominator_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < denominator a b c := by
  unfold denominator
  positivity

theorem gap_identity {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    denominator a b c * (value a b c - 3 - correction a b c) =
      (a ^ 2 - b * c) ^ 2 + b * c * (a - b) ^ 2 := by
  have hab : a + b ≠ 0 := by positivity
  unfold denominator value correction
  field_simp
  ring

theorem source_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 + correction a b c ≤ value a b c := by
  have hg := gap_identity ha hb hc
  have hn : 0 ≤ (a ^ 2 - b * c) ^ 2 + b * c * (a - b) ^ 2 := by positivity
  have hd := denominator_pos ha hb hc
  nlinarith only [hg, hn, hd]

theorem equality_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    value a b c = 3 + correction a b c ↔ a = b ∧ b = c := by
  constructor
  · intro he
    have hg := gap_identity ha hb hc
    rw [he] at hg
    have h0 : 3 + correction a b c - 3 - correction a b c = 0 := by ring
    rw [h0, mul_zero] at hg
    have h1 := sq_nonneg (a ^ 2 - b * c)
    have h2 : 0 ≤ b * c * (a - b) ^ 2 := by positivity
    have hs : b * c * (a - b) ^ 2 = 0 := by linarith only [hg, h1, h2]
    have hs' := (mul_eq_zero.mp hs).resolve_left (ne_of_gt (mul_pos hb hc))
    have hab : a = b := by nlinarith only [hs']
    have he' : a ^ 2 = b * c := by nlinarith only [hg, h1, h2]
    refine ⟨hab, ?_⟩
    rw [hab] at he'
    nlinarith only [he', hb]
  · rintro ⟨rfl, rfl⟩
    norm_num [value, correction, ne_of_gt hc]
    field_simp
    ring

theorem correction_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hne : c ≠ a) : 0 < correction a b c := by
  unfold correction
  exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) (by positivity)

theorem ratio_gt_one {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hne : c ≠ a) : 1 < ratio a b c := by
  have hstrict : 3 + correction a b c < value a b c := by
    apply lt_of_le_of_ne (source_bound ha hb hc)
    intro he
    obtain ⟨hab, hbc⟩ := (equality_iff ha hb hc).mp he.symm
    exact hne (hbc.symm.trans hab.symm)
  unfold ratio
  apply (lt_div_iff₀ (correction_pos ha hb hc hne)).mpr
  linarith only [hstrict]

theorem product_one_slice {t : ℝ} (ht : 0 < t) (hne : t ≠ 1) :
    ratio 1 t (1 / t) = 1 + t := by
  have hi : 0 < 1 / t := by positivity
  have hi1 : 1 / t ≠ 1 := by
    intro he
    have := (div_eq_iff (ne_of_gt ht)).mp he
    apply hne
    linarith
  have hv : value 1 t (1 / t) - 3 = (1 + t) * correction 1 t (1 / t) := by
    have ht1 : 1 + t ≠ 0 := by positivity
    unfold value correction
    field_simp
    ring
  unfold ratio
  exact (div_eq_iff (ne_of_gt (correction_pos (by norm_num) ht hi hi1))).mpr hv

theorem equal_ab_slice {c : ℝ} (hc : 0 < c) (hne : c ≠ 1) :
    ratio 1 1 c = 2 := by
  have hv : value 1 1 c - 3 = 2 * correction 1 1 c := by
    unfold value correction
    field_simp
    ring
  unfold ratio
  exact (div_eq_iff (ne_of_gt (correction_pos (by norm_num) (by norm_num) hc hne))).mpr hv

theorem ratio_attains {z : ℝ} (hz : 1 < z) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ c ≠ a ∧ ratio a b c = z := by
  by_cases hz2 : z = 2
  · refine ⟨1, 1, 2, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [equal_ab_slice (by norm_num) (by norm_num), hz2]
  · have ht : 0 < z - 1 := by linarith
    have ht1 : z - 1 ≠ 1 := by intro he; apply hz2; linarith
    have hi : 0 < 1 / (z - 1) := by positivity
    have hi1 : 1 / (z - 1) ≠ 1 := by
      intro he
      have := (div_eq_iff (ne_of_gt ht)).mp he
      apply ht1
      linarith
    refine ⟨1, z - 1, 1 / (z - 1), by norm_num, ht, hi, hi1, ?_⟩
    rw [product_one_slice ht ht1]
    ring

theorem attained_ratio_range :
    {z : ℝ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ c ≠ a ∧ ratio a b c = z} =
      Set.Ioi 1 := by
  ext z
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, hne, rfl⟩
    exact ratio_gt_one ha hb hc hne
  · exact ratio_attains

theorem sharp_coefficient (k : ℝ) :
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
      3 + k * correction a b c ≤ value a b c) ↔ k ≤ 1 := by
  constructor
  · intro h
    by_contra hn
    have hk : 1 < k := by linarith
    obtain ⟨a, b, c, ha, hb, hc, hne, he⟩ := ratio_attains
      (show 1 < (k + 1) / 2 by linarith)
    have hv := h a b c ha hb hc
    have hr : k ≤ ratio a b c := by
      unfold ratio
      apply (le_div_iff₀ (correction_pos ha hb hc hne)).mpr
      linarith only [hv]
    rw [he] at hr
    linarith
  · intro hk a b c ha hb hc
    have hp : 0 ≤ correction a b c := by unfold correction; positivity
    have hm := mul_le_mul_of_nonneg_right hk hp
    have hv := source_bound ha hb hc
    nlinarith only [hm, hv]

end RefinedAMGMSharpCoefficient

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b + c) / a + a ^ 2 / (b * c) ≥ 3 + (c - a) ^ 2 / (c * (a + b)) :=
  RefinedAMGMSharpCoefficient.source_bound ha hb hc

#print axioms RefinedAMGMSharpCoefficient.value
#print axioms RefinedAMGMSharpCoefficient.correction
#print axioms RefinedAMGMSharpCoefficient.ratio
#print axioms RefinedAMGMSharpCoefficient.denominator
#print axioms RefinedAMGMSharpCoefficient.denominator_pos
#print axioms RefinedAMGMSharpCoefficient.gap_identity
#print axioms RefinedAMGMSharpCoefficient.source_bound
#print axioms RefinedAMGMSharpCoefficient.equality_iff
#print axioms RefinedAMGMSharpCoefficient.correction_pos
#print axioms RefinedAMGMSharpCoefficient.ratio_gt_one
#print axioms RefinedAMGMSharpCoefficient.product_one_slice
#print axioms RefinedAMGMSharpCoefficient.equal_ab_slice
#print axioms RefinedAMGMSharpCoefficient.ratio_attains
#print axioms RefinedAMGMSharpCoefficient.attained_ratio_range
#print axioms RefinedAMGMSharpCoefficient.sharp_coefficient
#print axioms solution
