-- Prove2me | solution 1 for lean_workbook_plus_72192
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:48:14.083864+00:00
-- url     : https://prove2.me/submissions/7e5731e2-c885-4c7c-9a53-3452af12ee9b

import Mathlib

set_option autoImplicit false

namespace RadicalScaleThresholdClassification

theorem positive_scale_representation {s : ℝ} (hs : 0 < s) :
    ∃ t : ℝ, 0 < t ∧ t ^ 2 = s :=
  ⟨Real.sqrt s, Real.sqrt_pos.2 hs, Real.sq_sqrt hs.le⟩

theorem square_sum_positive {x y z : ℝ} (hx : 0 < x) :
    0 < x ^ 2 + y ^ 2 + z ^ 2 := by
  nlinarith only [sq_pos_of_pos hx, sq_nonneg y, sq_nonneg z]

theorem scaled_sqrt {x y z t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (ht : 0 < t) :
    Real.sqrt ((t ^ 2 * x) * (t ^ 2 * y) * (t ^ 2 * z)) =
      t ^ 3 * Real.sqrt (x * y * z) := by
  have hp : 0 < x * y * z := mul_pos (mul_pos hx hy) hz
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  rw [mul_pow, Real.sq_sqrt hp.le]
  ring

theorem antecedent_on_ray {x y z t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (ht : 0 < t) :
    4 * Real.sqrt ((t ^ 2 * x) * (t ^ 2 * y) * (t ^ 2 * z)) ≤
        (t ^ 2 * x) ^ 2 + (t ^ 2 * y) ^ 2 + (t ^ 2 * z) ^ 2 ↔
      4 * Real.sqrt (x * y * z) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ t := by
  rw [scaled_sqrt hx hy hz ht]
  have hq := square_sum_positive (y := y) (z := z) hx
  rw [show 4 * (t ^ 3 * Real.sqrt (x * y * z)) =
      t ^ 3 * (4 * Real.sqrt (x * y * z)) by ring,
    show (t ^ 2 * x) ^ 2 + (t ^ 2 * y) ^ 2 + (t ^ 2 * z) ^ 2 =
      t ^ 3 * (t * (x ^ 2 + y ^ 2 + z ^ 2)) by ring,
    mul_le_mul_iff_right₀ (pow_pos ht 3), div_le_iff₀ hq]

theorem conclusion_on_ray {x y z t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (ht : 0 < t) :
    2 * Real.sqrt ((t ^ 2 * x) * (t ^ 2 * y) * (t ^ 2 * z)) ≤
        t ^ 2 * x + t ^ 2 * y + t ^ 2 * z ↔
      t ≤ (x + y + z) / (2 * Real.sqrt (x * y * z)) := by
  rw [scaled_sqrt hx hy hz ht]
  have hp : 0 < Real.sqrt (x * y * z) :=
    Real.sqrt_pos.2 (mul_pos (mul_pos hx hy) hz)
  rw [show 2 * (t ^ 3 * Real.sqrt (x * y * z)) =
      t ^ 2 * (t * (2 * Real.sqrt (x * y * z))) by ring,
    show t ^ 2 * x + t ^ 2 * y + t ^ 2 * z =
      t ^ 2 * (x + y + z) by ring,
    mul_le_mul_iff_right₀ (pow_pos ht 2), le_div_iff₀ (by positivity)]

theorem counterexample_on_ray_iff {x y z t : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) :
    (4 * Real.sqrt ((t ^ 2 * x) * (t ^ 2 * y) * (t ^ 2 * z)) ≤
        (t ^ 2 * x) ^ 2 + (t ^ 2 * y) ^ 2 + (t ^ 2 * z) ^ 2 ∧
      t ^ 2 * x + t ^ 2 * y + t ^ 2 * z <
        2 * Real.sqrt ((t ^ 2 * x) * (t ^ 2 * y) * (t ^ 2 * z))) ↔
      4 * Real.sqrt (x * y * z) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ t ∧
        (x + y + z) / (2 * Real.sqrt (x * y * z)) < t := by
  rw [antecedent_on_ray hx hy hz ht]
  have h := not_congr (conclusion_on_ray hx hy hz ht)
  simpa only [not_le] using and_congr_right (fun _ => h)

theorem unbounded_counterexamples_on_every_ray {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (M : ℝ) :
    ∃ t : ℝ, 0 < t ∧ M < t ∧
      0 < t ^ 2 * x ∧ 0 < t ^ 2 * y ∧ 0 < t ^ 2 * z ∧
      4 * Real.sqrt ((t ^ 2 * x) * (t ^ 2 * y) * (t ^ 2 * z)) ≤
        (t ^ 2 * x) ^ 2 + (t ^ 2 * y) ^ 2 + (t ^ 2 * z) ^ 2 ∧
      t ^ 2 * x + t ^ 2 * y + t ^ 2 * z <
        2 * Real.sqrt ((t ^ 2 * x) * (t ^ 2 * y) * (t ^ 2 * z)) := by
  let L := 4 * Real.sqrt (x * y * z) / (x ^ 2 + y ^ 2 + z ^ 2)
  let U := (x + y + z) / (2 * Real.sqrt (x * y * z))
  obtain ⟨t, ht⟩ := exists_gt (max 0 (max M (max L U)))
  have ht0 : 0 < t := lt_of_le_of_lt (le_max_left _ _) ht
  have htM : M < t := lt_of_le_of_lt
    ((le_max_left M _).trans (le_max_right _ _)) ht
  have htL : L < t := lt_of_le_of_lt
    (((le_max_left L U).trans (le_max_right M _)).trans (le_max_right _ _)) ht
  have htU : U < t := lt_of_le_of_lt
    (((le_max_right L U).trans (le_max_right M _)).trans (le_max_right _ _)) ht
  exact ⟨t, ht0, htM, by positivity, by positivity, by positivity,
    (counterexample_on_ray_iff hx hy hz ht0).2 ⟨htL.le, htU⟩⟩

theorem diagonal_counterexamples_iff {t : ℝ} (ht : 0 < t) :
    (4 * Real.sqrt (t ^ 2 * t ^ 2 * t ^ 2) ≤
        (t ^ 2) ^ 2 + (t ^ 2) ^ 2 + (t ^ 2) ^ 2 ∧
      t ^ 2 + t ^ 2 + t ^ 2 < 2 * Real.sqrt (t ^ 2 * t ^ 2 * t ^ 2)) ↔
      (3 : ℝ) / 2 < t := by
  have h := counterexample_on_ray_iff (x := 1) (y := 1) (z := 1)
    (by norm_num) (by norm_num) (by norm_num) ht
  norm_num at h
  rw [h]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by linarith, h⟩

theorem explicit_source_counterexample :
    (0 : ℝ) < 4 ∧ 4 * Real.sqrt ((4 : ℝ) * 4 * 4) ≤ 4 ^ 2 + 4 ^ 2 + 4 ^ 2 ∧
      (4 : ℝ) + 4 + 4 < 2 * Real.sqrt ((4 : ℝ) * 4 * 4) := by
  norm_num

theorem genuine_source_false :
    ¬ (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
      4 * Real.sqrt (a * b * c) ≤ a ^ 2 + b ^ 2 + c ^ 2 →
        2 * Real.sqrt (a * b * c) ≤ a + b + c) := by
  intro h
  have hf := explicit_source_counterexample
  exact (not_le_of_gt hf.2.2) (h 4 4 4 hf.1 hf.1 hf.1 hf.2.1)

theorem normalized_sum_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (habc : a * b * c = 1) : 3 ≤ a + b + c := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) ha.le hb.le hc.le (by norm_num)
  rw [← Real.mul_rpow ha.le hb.le,
    ← Real.mul_rpow (mul_nonneg ha.le hb.le) hc.le, habc, Real.one_rpow] at h
  linarith

theorem normalized_strict_conclusion {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (habc : a * b * c = 1) :
    2 * Real.sqrt (a * b * c) < a + b + c := by
  have h := normalized_sum_bound ha hb hc habc
  rw [habc, Real.sqrt_one]
  linarith

theorem normalized_hypotheses_inhabited :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a * b * c = 1 ∧
      4 * Real.sqrt (a * b * c) ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  refine ⟨2, 1, 1 / 2, ?_⟩
  norm_num

end RadicalScaleThresholdClassification

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1)
    (_h : a ^ 2 + b ^ 2 + c ^ 2 ≥ 4 * Real.sqrt (a * b * c)) :
    a + b + c ≥ 2 * Real.sqrt (a * b * c) :=
  (RadicalScaleThresholdClassification.normalized_strict_conclusion ha hb hc habc).le

#print axioms RadicalScaleThresholdClassification.positive_scale_representation
#print axioms RadicalScaleThresholdClassification.square_sum_positive
#print axioms RadicalScaleThresholdClassification.scaled_sqrt
#print axioms RadicalScaleThresholdClassification.antecedent_on_ray
#print axioms RadicalScaleThresholdClassification.conclusion_on_ray
#print axioms RadicalScaleThresholdClassification.counterexample_on_ray_iff
#print axioms RadicalScaleThresholdClassification.unbounded_counterexamples_on_every_ray
#print axioms RadicalScaleThresholdClassification.diagonal_counterexamples_iff
#print axioms RadicalScaleThresholdClassification.explicit_source_counterexample
#print axioms RadicalScaleThresholdClassification.genuine_source_false
#print axioms RadicalScaleThresholdClassification.normalized_sum_bound
#print axioms RadicalScaleThresholdClassification.normalized_strict_conclusion
#print axioms RadicalScaleThresholdClassification.normalized_hypotheses_inhabited
#print axioms solution
