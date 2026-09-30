-- Prove2me | solution 1 for lean_workbook_plus_23371
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:24:49.034474+00:00
-- url     : https://prove2.me/submissions/8f56644d-7ef6-4227-924e-4d70af55b335

import Mathlib

set_option autoImplicit false

namespace QuarticRefinementCoefficient

def gap (k a b c : ℝ) : ℝ :=
  a ^ 4 + b ^ 4 + c ^ 4 - a * b * c * (a + b + c) - k * a * b * (a - b) ^ 2

theorem square_identity (k a b c : ℝ) :
    16 * gap k a b c =
      (4 * c ^ 2 - (a + b) ^ 2) ^ 2 +
      (2 * (a + b) * c - (a + b) ^ 2 + 2 * (a - b) ^ 2) ^ 2 +
      (a - b) ^ 2 * (2 * c - (a + b)) ^ 2 +
      (4 * k - 2) * (a - b) ^ 4 + (15 - 4 * k) * (a + b) ^ 2 * (a - b) ^ 2 := by
  unfold gap
  ring

theorem lower_endpoint_identity (a b c : ℝ) :
    gap (-1 / 2) a b c = (a + b) ^ 4 + c ^ 4 +
      (-a * b) * ((c + (a + b) / 2) ^ 2 + 13 / 4 * (a + b) ^ 2) := by
  unfold gap
  ring

theorem coefficient_difference (k l a b c : ℝ) :
    gap k a b c = gap l a b c + (l - k) * (a * b) * (a - b) ^ 2 := by
  unfold gap
  ring

theorem upper_endpoint_nonnegative (a b c : ℝ) : 0 ≤ gap (15 / 4) a b c := by
  have h1 := sq_nonneg (4 * c ^ 2 - (a + b) ^ 2)
  have h2 := sq_nonneg (2 * (a + b) * c - (a + b) ^ 2 + 2 * (a - b) ^ 2)
  have h3 := mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (2 * c - (a + b)))
  have h4 : 0 ≤ (a - b) ^ 4 := by
    convert sq_nonneg ((a - b) ^ 2) using 1
    ring
  have hn := add_nonneg (add_nonneg (add_nonneg h1 h2) h3)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 13) h4)
  have hid : 16 * gap (15 / 4) a b c =
      (4 * c ^ 2 - (a + b) ^ 2) ^ 2 +
      (2 * (a + b) * c - (a + b) ^ 2 + 2 * (a - b) ^ 2) ^ 2 +
      (a - b) ^ 2 * (2 * c - (a + b)) ^ 2 + 13 * (a - b) ^ 4 := by
    linear_combination square_identity (15 / 4) a b c
  rw [← hid] at hn
  exact (mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 16)).mp hn

theorem lower_endpoint_nonnegative {a b : ℝ} (hab : a * b ≤ 0) (c : ℝ) :
    0 ≤ gap (-1 / 2) a b c := by
  rw [lower_endpoint_identity]
  have hn : 0 ≤ -a * b := by nlinarith only [hab]
  positivity

theorem nonnegative_of_interval {k : ℝ} (hl : -1 / 2 ≤ k) (hu : k ≤ 15 / 4)
    (a b c : ℝ) : 0 ≤ gap k a b c := by
  rcases le_total 0 (a * b) with hab | hab
  · rw [coefficient_difference k (15 / 4)]
    exact add_nonneg (upper_endpoint_nonnegative a b c)
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hu) hab) (sq_nonneg (a - b)))
  · rw [coefficient_difference k (-1 / 2)]
    exact add_nonneg (lower_endpoint_nonnegative hab c)
      (mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hl) hab)
        (sq_nonneg (a - b)))

theorem symmetric_slice (k t : ℝ) :
    gap k (1 + t) (1 - t) 1 = t ^ 2 * ((15 - 4 * k) + (2 + 4 * k) * t ^ 2) := by
  unfold gap
  ring

theorem upper_obstruction {k : ℝ} (hk : 15 / 4 < k) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ gap k a b c < 0 := by
  let q : ℝ := (4 * k - 15) / (2 * (2 + 4 * k))
  have hn : 0 < 4 * k - 15 := by linarith
  have hd : 0 < 2 * (2 + 4 * k) := by linarith
  have hq : 0 < q := div_pos hn hd
  have hqu : q < 1 := by
    dsimp [q]
    apply (div_lt_iff₀ hd).mpr
    linarith
  let t := Real.sqrt q
  have ht : 0 < t := Real.sqrt_pos.mpr hq
  have ht2 : t ^ 2 = q := Real.sq_sqrt hq.le
  have htu : t < 1 := by nlinarith only [ht, ht2, hqu]
  have he : 2 * (2 + 4 * k) * t ^ 2 = 4 * k - 15 := by
    rw [ht2]
    dsimp [q]
    field_simp
  have hneg : (15 - 4 * k) + (2 + 4 * k) * t ^ 2 < 0 := by
    nlinarith only [he, hn]
  refine ⟨1 + t, 1 - t, 1, by linarith, by linarith, by norm_num, ?_⟩
  rw [symmetric_slice]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos ht) hneg

theorem all_real_coefficients (k : ℝ) :
    (∀ a b c : ℝ, 0 ≤ gap k a b c) ↔ -1 / 2 ≤ k ∧ k ≤ 15 / 4 := by
  constructor
  · intro h
    constructor
    · have hh := h 1 (-1) 0
      unfold gap at hh
      nlinarith only [hh]
    · by_contra! hk
      obtain ⟨a, b, c, _, _, _, hn⟩ := upper_obstruction hk
      exact (not_lt_of_ge (h a b c)) hn
  · rintro ⟨hl, hu⟩
    exact nonnegative_of_interval hl hu

theorem nonnegative_domain_coefficients (k : ℝ) :
    (∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ gap k a b c) ↔ k ≤ 15 / 4 := by
  constructor
  · intro h
    by_contra! hk
    obtain ⟨a, b, c, ha, hb, hc, hn⟩ := upper_obstruction hk
    exact (not_lt_of_ge (h a b c ha.le hb.le hc.le)) hn
  · intro hk a b c ha hb _
    rw [coefficient_difference k (15 / 4)]
    exact add_nonneg (upper_endpoint_nonnegative a b c)
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hk) (mul_nonneg ha hb))
        (sq_nonneg (a - b)))

theorem source_nonnegative (a b c : ℝ) : 0 ≤ gap (14 / 5) a b c :=
  nonnegative_of_interval (by norm_num) (by norm_num) a b c

theorem diagonal_identity (k a c : ℝ) :
    gap k a a c = (c - a) ^ 2 * ((c + a) ^ 2 + a ^ 2) := by
  unfold gap
  ring

theorem source_equality_iff (a b c : ℝ) :
    gap (14 / 5) a b c = 0 ↔ a = b ∧ b = c := by
  constructor
  · intro he
    have h1 := sq_nonneg (4 * c ^ 2 - (a + b) ^ 2)
    have h2 := sq_nonneg (2 * (a + b) * c - (a + b) ^ 2 + 2 * (a - b) ^ 2)
    have h3 := mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (2 * c - (a + b)))
    have h4 := sq_nonneg ((a - b) ^ 2)
    have h5 := mul_nonneg (sq_nonneg (a + b)) (sq_nonneg (a - b))
    have hz : (a - b) ^ 4 = 0 := by
      nlinarith only [square_identity (14 / 5) a b c, he, h1, h2, h3, h4, h5]
    have hab : a = b := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
    subst b
    rw [diagonal_identity] at he
    rcases mul_eq_zero.mp he with he | he
    · have hc : c = a := sub_eq_zero.mp (eq_zero_of_pow_eq_zero he)
      exact ⟨rfl, hc.symm⟩
    · have ha : a = 0 := by nlinarith only [he, sq_nonneg (c + a)]
      subst a
      have hc : c = 0 := by nlinarith only [he]
      exact ⟨rfl, hc.symm⟩
  · rintro ⟨rfl, rfl⟩
    unfold gap
    ring

theorem source_strict_iff (a b c : ℝ) :
    0 < gap (14 / 5) a b c ↔ ¬ (a = b ∧ b = c) := by
  rw [← source_equality_iff]
  exact (lt_iff_le_and_ne).trans (by simp [source_nonnegative a b c, ne_comm])

theorem nonnegative_value_attained {w : ℝ} (hw : 0 ≤ w) (k : ℝ) :
    ∃ a b c : ℝ, gap k a b c = w := by
  let a := Real.sqrt (Real.sqrt w)
  have ha : a ^ 2 = Real.sqrt w := Real.sq_sqrt (Real.sqrt_nonneg w)
  have hw2 : (Real.sqrt w) ^ 2 = w := Real.sq_sqrt hw
  refine ⟨a, 0, 0, ?_⟩
  simp only [gap, zero_pow (by omega : 4 ≠ 0), mul_zero, zero_mul, sub_zero,
    add_zero]
  nlinarith only [ha, hw2, sq_nonneg (a ^ 2 - Real.sqrt w)]

theorem source_range :
    {w : ℝ | ∃ a b c : ℝ, gap (14 / 5) a b c = w} = Set.Ici 0 := by
  ext w
  constructor
  · rintro ⟨a, b, c, rfl⟩
    exact source_nonnegative a b c
  · intro hw
    exact nonnegative_value_attained hw (14 / 5)

theorem source_least : IsLeast {w : ℝ | ∃ a b c : ℝ, gap (14 / 5) a b c = w} 0 := by
  rw [source_range]
  exact ⟨by simp, fun _ h => h⟩

end QuarticRefinementCoefficient

theorem solution : ∀ a b c : ℝ, a ^ 4 + b ^ 4 + c ^ 4 ≥
    a * b * c * (a + b + c) + (14 / 5) * a * b * (a - b) ^ 2 := by
  intro a b c
  have h := QuarticRefinementCoefficient.source_nonnegative a b c
  unfold QuarticRefinementCoefficient.gap at h
  linarith
