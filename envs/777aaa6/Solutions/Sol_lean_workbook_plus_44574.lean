-- Prove2me | solution 1 for lean_workbook_plus_44574
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:11:30.617438+00:00
-- url     : https://prove2.me/submissions/8ff3f36b-b87b-4c24-9a30-33e13587ee46

import Mathlib

namespace FourthPowerBudgetRange

noncomputable def value (a b c : ℝ) : ℝ := a * b * c + 1 / (a * b * c)

noncomputable def scale : ℝ := Real.sqrt 2 / 2

theorem scale_data : 0 < scale ∧ scale ^ 2 = 1 / 2 ∧ scale ^ 4 = 1 / 4 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  dsimp [scale]
  refine ⟨by positivity, ?_, ?_⟩
  · nlinarith only [hs]
  · nlinarith only [hs, sq_nonneg ((Real.sqrt 2) ^ 2 - 2)]

theorem budget_identity (a b c : ℝ) :
    1 / 2 - a * b * c =
      a * b * (3 / 2 - a ^ 4 - b ^ 4 - c) +
      a * b * (a ^ 2 - b ^ 2) ^ 2 +
      (a * b - 1 / 2) ^ 2 * (2 * a * b + 2) := by ring

theorem product_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 4 + b ^ 4 + c ≤ 3 / 2) : a * b * c ≤ 1 / 2 := by
  have hab := mul_pos ha hb
  have h1 := mul_nonneg hab.le (show 0 ≤ 3 / 2 - a ^ 4 - b ^ 4 - c by linarith)
  have h2 := mul_nonneg hab.le (sq_nonneg (a ^ 2 - b ^ 2))
  have h3 := mul_nonneg (sq_nonneg (a * b - 1 / 2))
    (show 0 ≤ 2 * a * b + 2 by linarith)
  linarith only [budget_identity a b c, h1, h2, h3]

theorem product_equality_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 4 + b ^ 4 + c ≤ 3 / 2) :
    a * b * c = 1 / 2 ↔ a = scale ∧ b = scale ∧ c = 1 := by
  constructor
  · intro he
    have hab := mul_pos ha hb
    have hp : 0 < 2 * a * b + 2 := by linarith
    have h1 := mul_nonneg hab.le (show 0 ≤ 3 / 2 - a ^ 4 - b ^ 4 - c by linarith)
    have h2 := mul_nonneg hab.le (sq_nonneg (a ^ 2 - b ^ 2))
    have h3 := mul_nonneg (sq_nonneg (a * b - 1 / 2)) hp.le
    have hz : (a * b - 1 / 2) ^ 2 * (2 * a * b + 2) = 0 := by
      linarith only [budget_identity a b c, he, h1, h2, h3]
    have habhalf : a * b = 1 / 2 := by
      have := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hz).resolve_right (ne_of_gt hp))
      linarith
    have hz2 : a * b * (a ^ 2 - b ^ 2) ^ 2 = 0 := by
      linarith only [budget_identity a b c, he, h1, h2, h3]
    have hs : a ^ 2 - b ^ 2 = 0 :=
      eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hz2).resolve_left (ne_of_gt hab))
    have habEq : a = b := by nlinarith only [hs, ha, hb]
    have har : a = scale := by
      have hr := scale_data
      nlinarith only [habhalf, habEq, hr.1, hr.2.1, ha]
    refine ⟨har, habEq.symm.trans har, ?_⟩
    nlinarith only [he, habhalf]
  · rintro ⟨rfl, rfl, rfl⟩
    nlinarith only [scale_data.2.1]

theorem reciprocal_identity {t : ℝ} (ht : t ≠ 0) :
    t * (t + 1 / t - 5 / 2) = (1 / 2 - t) * (2 - t) := by
  field_simp
  ring

theorem reciprocal_bound {t : ℝ} (ht : 0 < t) (hu : t ≤ 1 / 2) :
    5 / 2 ≤ t + 1 / t := by
  have hg := reciprocal_identity (ne_of_gt ht)
  have hn := mul_nonneg (show 0 ≤ 1 / 2 - t by linarith)
    (show 0 ≤ 2 - t by linarith)
  nlinarith only [hg, hn, ht]

theorem reciprocal_equality_iff {t : ℝ} (ht : 0 < t) (hu : t ≤ 1 / 2) :
    t + 1 / t = 5 / 2 ↔ t = 1 / 2 := by
  constructor
  · intro he
    have hg := reciprocal_identity (ne_of_gt ht)
    have hz : (1 / 2 - t) * (2 - t) = 0 := by
      rw [he] at hg
      simpa only [sub_self, mul_zero] using hg.symm
    have hp : 2 - t ≠ 0 := by linarith
    have := (mul_eq_zero.mp hz).resolve_right hp
    linarith
  · rintro rfl
    norm_num

theorem source_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 4 + b ^ 4 + c ≤ 3 / 2) : 5 / 2 ≤ value a b c :=
  reciprocal_bound (mul_pos (mul_pos ha hb) hc) (product_bound ha hb h)

theorem equality_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 4 + b ^ 4 + c ≤ 3 / 2) :
    value a b c = 5 / 2 ↔ a = scale ∧ b = scale ∧ c = 1 := by
  rw [value, reciprocal_equality_iff (mul_pos (mul_pos ha hb) hc) (product_bound ha hb h)]
  exact product_equality_iff ha hb h

theorem slice_model {c : ℝ} (hc : 0 < c) (hu : c ≤ 1) :
    0 < scale ∧ scale ^ 4 + scale ^ 4 + c ≤ 3 / 2 ∧
      value scale scale c = c / 2 + 2 / c := by
  refine ⟨scale_data.1, by nlinarith only [scale_data.2.2, hu], ?_⟩
  have hs : scale * scale = 1 / 2 := by nlinarith only [scale_data.2.1]
  unfold value
  rw [hs]
  field_simp

theorem attains {w : ℝ} (hw : 5 / 2 ≤ w) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      a ^ 4 + b ^ 4 + c ≤ 3 / 2 ∧ value a b c = w := by
  let l : ℝ := 1 / (w + 1)
  have hw1 : 0 < w + 1 := by linarith
  have hl : 0 < l := one_div_pos.mpr hw1
  have hlu : l ≤ 1 := by
    dsimp [l]
    apply (div_le_iff₀ hw1).mpr
    linarith
  have hcont : ContinuousOn (fun c : ℝ => c / 2 + 2 / c) (Set.Icc l 1) := by
    apply ContinuousOn.add (continuous_id.div_const 2).continuousOn
    exact continuousOn_const.div continuousOn_id (fun c hc => ne_of_gt (hl.trans_le hc.1))
  have hv : l / 2 + 2 / l ≥ w := by
    have hinv : 1 / l = w + 1 := by dsimp [l]; field_simp
    have he : 2 / l = 2 * (w + 1) := by rw [div_eq_mul_one_div, hinv]
    linarith
  obtain ⟨c, hci, he⟩ := intermediate_value_Icc' hlu hcont
    (show w ∈ Set.Icc ((1 : ℝ) / 2 + 2 / 1) (l / 2 + 2 / l) by
      constructor <;> linarith)
  have hc := hl.trans_le hci.1
  obtain ⟨hr, hb, hv⟩ := slice_model hc hci.2
  exact ⟨scale, scale, c, hr, hr, hc, hb, hv.trans he⟩

theorem attained_range :
    {w : ℝ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      a ^ 4 + b ^ 4 + c ≤ 3 / 2 ∧ value a b c = w} = Set.Ici (5 / 2) := by
  ext w
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, h, rfl⟩
    exact source_bound ha hb hc h
  · exact attains

theorem least_value : IsLeast {w : ℝ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    a ^ 4 + b ^ 4 + c ≤ 3 / 2 ∧ value a b c = w} (5 / 2) := by
  rw [attained_range]
  exact ⟨by simp, fun _ h => h⟩

theorem sharp_lower_constant (k : ℝ) :
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
      a ^ 4 + b ^ 4 + c ≤ 3 / 2 → k ≤ value a b c) ↔ k ≤ 5 / 2 := by
  constructor
  · intro h
    obtain ⟨a, b, c, ha, hb, hc, hh, he⟩ := attains (le_refl (5 / 2 : ℝ))
    simpa only [he] using h a b c ha hb hc hh
  · intro hk a b c ha hb hc hh
    exact hk.trans (source_bound ha hb hc hh)

end FourthPowerBudgetRange

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_habc : a * b * c = 1) (h : a ^ 4 + b ^ 4 + c ≤ 3 / 2) :
    a * b * c + 1 / (a * b * c) ≥ 5 / 2 :=
  FourthPowerBudgetRange.source_bound ha hb hc h

#print axioms FourthPowerBudgetRange.value
#print axioms FourthPowerBudgetRange.scale
#print axioms FourthPowerBudgetRange.scale_data
#print axioms FourthPowerBudgetRange.budget_identity
#print axioms FourthPowerBudgetRange.product_bound
#print axioms FourthPowerBudgetRange.product_equality_iff
#print axioms FourthPowerBudgetRange.reciprocal_identity
#print axioms FourthPowerBudgetRange.reciprocal_bound
#print axioms FourthPowerBudgetRange.reciprocal_equality_iff
#print axioms FourthPowerBudgetRange.source_bound
#print axioms FourthPowerBudgetRange.equality_iff
#print axioms FourthPowerBudgetRange.slice_model
#print axioms FourthPowerBudgetRange.attains
#print axioms FourthPowerBudgetRange.attained_range
#print axioms FourthPowerBudgetRange.least_value
#print axioms FourthPowerBudgetRange.sharp_lower_constant
#print axioms solution
