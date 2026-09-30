-- Prove2me | solution 1 for lean_workbook_plus_61356
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:57:16.255243+00:00
-- url     : https://prove2.me/submissions/d806c3a0-09df-4636-9e10-b615c1a53ea6

import Mathlib

namespace CubicMixedProductRatio

def sumCubes (a b c : ℝ) : ℝ := a ^ 3 + b ^ 3 + c ^ 3

def mixedProduct (a b c : ℝ) : ℝ :=
  (a ^ 2 + b * c) * (b ^ 2 + a * c) * (c ^ 2 + a * b)

noncomputable def ratio (a b c : ℝ) : ℝ := sumCubes a b c / mixedProduct a b c

theorem product_identity (a b c : ℝ) :
    mixedProduct a b c = 2 * (a * b * c) ^ 2 +
      (a * b * c) * sumCubes a b c + (a * b) ^ 3 + (a * c) ^ 3 + (b * c) ^ 3 := by
  unfold mixedProduct sumCubes
  ring

theorem sum_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < sumCubes a b c := by
  unfold sumCubes
  positivity

theorem product_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < mixedProduct a b c := by
  unfold mixedProduct
  positivity

theorem strict_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) : sumCubes a b c < mixedProduct a b c := by
  rw [product_identity, habc]
  have hp : 0 < (a * b) ^ 3 := by positivity
  have hq : 0 < (a * c) ^ 3 := by positivity
  have hr : 0 < (b * c) ^ 3 := by positivity
  nlinarith

theorem ratio_bounds {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) : ratio a b c ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨div_pos (sum_pos ha hb hc) (product_pos ha hb hc),
    (div_lt_one (product_pos ha hb hc)).mpr (strict_bound ha hb hc habc)⟩

def levelPolynomial (z u : ℝ) : ℝ :=
  u ^ 4 + 2 * u - z * (u ^ 2 + 1) * (u + 1) ^ 2

theorem level_eventually_pos {z u : ℝ} (hz : z < 1) (hu : 1 ≤ u)
    (hzu : 6 ≤ (1 - z) * u) : 0 < levelPolynomial z u := by
  have hu0 : 0 < u := by linarith
  have hd : 0 < 1 - z := by linarith
  have hlarge : 0 < (1 - z) * u - 5 := by linarith
  have huz : 0 < u - z := by linarith
  have hu3 : 1 ≤ u ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ u ^ 2 + u + 1 by positivity)]
  have h1 : 0 < ((1 - z) * u - 5) * u ^ 3 := by positivity
  have h2 : 0 ≤ 2 * (1 - z) * u ^ 3 := by positivity
  have h3 : 0 ≤ 2 * u ^ 2 * (u - z) := by positivity
  have h4 : 0 ≤ u ^ 3 - z := by linarith
  have h5 : 0 ≤ 2 * (1 - z) * u := by positivity
  have he : levelPolynomial z u =
      ((1 - z) * u - 5) * u ^ 3 + 2 * (1 - z) * u ^ 3 +
      2 * u ^ 2 * (u - z) + (u ^ 3 - z) + 2 * (1 - z) * u := by
    unfold levelPolynomial
    ring
  linarith

theorem level_has_positive_root {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ u : ℝ, 0 < u ∧ levelPolynomial z u = 0 := by
  let T : ℝ := 6 / (1 - z)
  have hd : 0 < 1 - z := by linarith [hz.2]
  have hT : 1 ≤ T := by
    dsimp [T]
    apply (le_div_iff₀ hd).mpr
    linarith [hz.1]
  have he : (1 - z) * T = 6 := by
    dsimp [T]
    field_simp
  have hright := level_eventually_pos hz.2 hT he.ge
  have hleft : levelPolynomial z 0 < 0 := by
    unfold levelPolynomial
    nlinarith [hz.1]
  have hcont : Continuous (levelPolynomial z) := by
    unfold levelPolynomial
    fun_prop
  obtain ⟨u, hu, hu0⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ T by linarith)
    hcont.continuousOn (show (0 : ℝ) ∈ Set.Icc (levelPolynomial z 0)
      (levelPolynomial z T) from ⟨hleft.le, hright.le⟩)
  refine ⟨u, ?_, hu0⟩
  have hne : u ≠ 0 := by
    intro heq
    rw [heq] at hu0
    linarith
  exact lt_of_le_of_ne hu.1 (Ne.symm hne)

theorem family_product {t : ℝ} (ht : 0 < t) :
    t ^ 2 * (1 / t) * (1 / t) = 1 := by
  field_simp

theorem family_scaled_sum {t : ℝ} (ht : 0 < t) :
    sumCubes (t ^ 2) (1 / t) (1 / t) * t ^ 6 = (t ^ 3) ^ 4 + 2 * t ^ 3 := by
  unfold sumCubes
  field_simp
  ring

theorem family_scaled_product {t : ℝ} (ht : 0 < t) :
    mixedProduct (t ^ 2) (1 / t) (1 / t) * t ^ 6 =
      ((t ^ 3) ^ 2 + 1) * (t ^ 3 + 1) ^ 2 := by
  unfold mixedProduct
  field_simp
  ring

theorem attains {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a * b * c = 1 ∧ ratio a b c = z := by
  obtain ⟨u, hu, he⟩ := level_has_positive_root hz
  let t : ℝ := u ^ ((3 : ℝ)⁻¹)
  have ht : 0 < t := Real.rpow_pos_of_pos hu _
  have ht3 : t ^ 3 = u :=
    Real.rpow_inv_natCast_pow hu.le (by norm_num : (3 : ℕ) ≠ 0)
  have hs := family_scaled_sum ht
  have hp := family_scaled_product ht
  rw [ht3] at hs hp
  have hv : sumCubes (t ^ 2) (1 / t) (1 / t) =
      z * mixedProduct (t ^ 2) (1 / t) (1 / t) := by
    apply (mul_right_cancel₀ (show t ^ 6 ≠ 0 by positivity))
    rw [mul_assoc, hs, hp]
    unfold levelPolynomial at he
    nlinarith [he]
  refine ⟨t ^ 2, 1 / t, 1 / t, by positivity, by positivity, by positivity,
    family_product ht, ?_⟩
  unfold ratio
  apply (div_eq_iff (product_pos (by positivity) (by positivity) (by positivity)).ne').mpr
  exact hv

theorem attained_range :
    {z : ℝ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a * b * c = 1 ∧
      ratio a b c = z} = Set.Ioo 0 1 := by
  ext z
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, hp, rfl⟩
    exact ratio_bounds ha hb hc hp
  · exact attains

theorem sharp_ratio_bound (k : ℝ) :
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → a * b * c = 1 →
      sumCubes a b c ≤ k * mixedProduct a b c) ↔ 1 ≤ k := by
  constructor
  · intro h
    by_contra hk
    have hk1 : k < 1 := lt_of_not_ge hk
    let z : ℝ := (max k 0 + 1) / 2
    have hm : max k 0 < 1 := max_lt hk1 (by norm_num)
    have hz : z ∈ Set.Ioo (0 : ℝ) 1 := by
      dsimp [z]
      constructor <;> linarith [le_max_right k 0]
    have hkz : k < z := by
      dsimp [z]
      linarith [le_max_left k 0]
    obtain ⟨a, b, c, ha, hb, hc, hp, hv⟩ := attains hz
    have hvk : ratio a b c ≤ k := (div_le_iff₀ (product_pos ha hb hc)).mpr
      (h a b c ha hb hc hp)
    rw [hv] at hvk
    linarith
  · intro hk a b c ha hb hc hp
    have hd := product_pos ha hb hc
    have hs := strict_bound ha hb hc hp
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) hd.le]

theorem sharp_source_coefficient (k : ℝ) :
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → a * b * c = 1 →
      8 * sumCubes a b c ≤ k * mixedProduct a b c) ↔ 8 ≤ k := by
  constructor
  · intro h
    have hk := (sharp_ratio_bound (k / 8)).mp (by
      intro a b c ha hb hc hp
      have he := h a b c ha hb hc hp
      linarith)
    linarith
  · intro hk a b c ha hb hc hp
    have he := (sharp_ratio_bound (k / 8)).mpr (by linarith) a b c ha hb hc hp
    linarith

theorem source_strict {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    8 * sumCubes a b c < 9 * mixedProduct a b c := by
  have hs := strict_bound ha hb hc habc
  have hd := product_pos ha hb hc
  linarith

end CubicMixedProductRatio

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) : 8 * (a ^ 3 + b ^ 3 + c ^ 3) ≤
    9 * (a ^ 2 + b * c) * (b ^ 2 + a * c) * (c ^ 2 + a * b) := by
  have h := CubicMixedProductRatio.source_strict ha hb hc habc
  unfold CubicMixedProductRatio.sumCubes CubicMixedProductRatio.mixedProduct at h
  nlinarith

#print axioms CubicMixedProductRatio.sumCubes
#print axioms CubicMixedProductRatio.mixedProduct
#print axioms CubicMixedProductRatio.ratio
#print axioms CubicMixedProductRatio.product_identity
#print axioms CubicMixedProductRatio.sum_pos
#print axioms CubicMixedProductRatio.product_pos
#print axioms CubicMixedProductRatio.strict_bound
#print axioms CubicMixedProductRatio.ratio_bounds
#print axioms CubicMixedProductRatio.levelPolynomial
#print axioms CubicMixedProductRatio.level_eventually_pos
#print axioms CubicMixedProductRatio.level_has_positive_root
#print axioms CubicMixedProductRatio.family_product
#print axioms CubicMixedProductRatio.family_scaled_sum
#print axioms CubicMixedProductRatio.family_scaled_product
#print axioms CubicMixedProductRatio.attains
#print axioms CubicMixedProductRatio.attained_range
#print axioms CubicMixedProductRatio.sharp_ratio_bound
#print axioms CubicMixedProductRatio.sharp_source_coefficient
#print axioms CubicMixedProductRatio.source_strict
#print axioms solution
