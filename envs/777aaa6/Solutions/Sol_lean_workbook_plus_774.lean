-- Prove2me | solution 1 for lean_workbook_plus_774
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:21:49.390962+00:00
-- url     : https://prove2.me/submissions/e6b6793c-f830-40de-b71b-5f2efec40290

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace ShiftedReciprocalRange

def core (p q : ℝ) : ℝ := 1 / (p + q) - 1 / (p * q)

def value (x y : ℝ) : ℝ := core (x + 1) (y + 1)

def attainable : Set ℝ := {v | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ value x y = v}

theorem upper_gap (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    1 / 16 - core p q = (p + q - 8) ^ 2 / (16 * (p + q) ^ 2) +
      (p - q) ^ 2 / ((p + q) ^ 2 * p * q) := by
  have hs : 0 < p + q := by positivity
  dsimp [core]
  field_simp
  ring

theorem upper_bound (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : core p q ≤ 1 / 16 := by
  have h := upper_gap p q hp hq
  have h1 : 0 ≤ (p + q - 8) ^ 2 / (16 * (p + q) ^ 2) := by positivity
  have h2 : 0 ≤ (p - q) ^ 2 / ((p + q) ^ 2 * p * q) := by positivity
  linarith only [h, h1, h2]

theorem upper_equality (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    core p q = 1 / 16 ↔ p = 4 ∧ q = 4 := by
  constructor
  · intro he
    have h := upper_gap p q hp hq
    rw [he, sub_self] at h
    have h1 : 0 ≤ (p + q - 8) ^ 2 / (16 * (p + q) ^ 2) := by positivity
    have h2 : 0 ≤ (p - q) ^ 2 / ((p + q) ^ 2 * p * q) := by positivity
    obtain ⟨hz1, hz2⟩ := (add_eq_zero_iff_of_nonneg h1 h2).mp h.symm
    have hs : p + q - 8 = 0 := by
      have hd : 16 * (p + q) ^ 2 ≠ 0 := ne_of_gt (by positivity)
      exact eq_zero_of_pow_eq_zero ((div_eq_zero_iff.mp hz1).resolve_right hd)
    have hd : p - q = 0 := by
      have hden : (p + q) ^ 2 * p * q ≠ 0 := ne_of_gt (by positivity)
      exact eq_zero_of_pow_eq_zero ((div_eq_zero_iff.mp hz2).resolve_right hden)
    constructor <;> linarith only [hs, hd]
  · rintro ⟨rfl, rfl⟩
    norm_num [core]

theorem lower_gap (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    value x y + 1 / 2 =
      (x ^ 2 * y + x * y ^ 2 + x ^ 2 + y ^ 2 + 6 * x * y + 3 * x + 3 * y) /
      (2 * (x + y + 2) * (x + 1) * (y + 1)) := by
  have h1 : 0 < x + 1 := by positivity
  have h2 : 0 < y + 1 := by positivity
  have hs : 0 < x + y + 2 := by positivity
  have hs' : 0 < (x + 1) + (y + 1) := by positivity
  dsimp [value, core]
  field_simp
  ring

theorem source_bounds (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    -(1 / 2) < value x y ∧ value x y ≤ 1 / 16 := by
  constructor
  · have h := lower_gap x y hx hy
    have hpos : 0 <
        (x ^ 2 * y + x * y ^ 2 + x ^ 2 + y ^ 2 + 6 * x * y + 3 * x + 3 * y) /
        (2 * (x + y + 2) * (x + 1) * (y + 1)) := by positivity
    linarith only [h, hpos]
  · exact upper_bound (x + 1) (y + 1) (by positivity) (by positivity)

theorem source_equality (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    value x y = 1 / 16 ↔ x = 3 ∧ y = 3 := by
  change core (x + 1) (y + 1) = 1 / 16 ↔ _
  rw [upper_equality (x + 1) (y + 1) (by positivity) (by positivity)]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]

theorem diagonal_value (t : ℝ) (ht : 0 < t) : core t t = (t - 2) / (2 * t ^ 2) := by
  have hs : 0 < t + t := by positivity
  dsimp [core]
  field_simp
  ring

theorem diagonal_preimage (v : ℝ) (hl : -(1 / 2) < v) (hu : v ≤ 1 / 16) :
    ∃ t : ℝ, 1 < t ∧ core t t = v := by
  let s := Real.sqrt (1 - 16 * v)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs : s ^ 2 = 1 - 16 * v := Real.sq_sqrt (by linarith only [hu])
  have hs3 : s < 3 := by nlinarith only [hs, hs0, hl]
  have hden : 0 < 1 + s := by positivity
  let t := 4 / (1 + s)
  have ht : 1 < t := by
    dsimp [t]
    apply (lt_div_iff₀ hden).mpr
    linarith only [hs3]
  refine ⟨t, ht, ?_⟩
  rw [diagonal_value t (by linarith only [ht])]
  apply (div_eq_iff (ne_of_gt (by positivity : 0 < 2 * t ^ 2))).mpr
  dsimp [t]
  field_simp
  nlinarith only [hs]

theorem range_classification : attainable = Set.Ioc (-(1 / 2)) (1 / 16) := by
  ext v
  constructor
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact source_bounds x y hx hy
  · rintro ⟨hl, hu⟩
    obtain ⟨t, ht, hvalue⟩ := diagonal_preimage v hl hu
    refine ⟨t - 1, t - 1, by linarith, by linarith, ?_⟩
    simpa [value] using hvalue

theorem greatest_value : IsGreatest attainable (1 / 16) := by
  rw [range_classification]
  constructor
  · norm_num
  · intro v hv
    exact hv.2

theorem no_least (v : ℝ) : ¬ IsLeast attainable v := by
  rw [range_classification]
  rintro ⟨hv, hl⟩
  have hm : (v - 1 / 2) / 2 ∈ Set.Ioc (-(1 / 2)) (1 / 16) := by
    constructor <;> linarith only [hv.1, hv.2]
  have := hl hm
  linarith only [this, hv.1]

theorem source_expression (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    value x y = (x + y + 2)⁻¹ - (x + 1)⁻¹ * (y + 1)⁻¹ := by
  have h1 : 0 < x + 1 := by positivity
  have h2 : 0 < y + 1 := by positivity
  have hs : 0 < x + y + 2 := by positivity
  have hs' : 0 < (x + 1) + (y + 1) := by positivity
  dsimp [value, core]
  field_simp
  ring

end ShiftedReciprocalRange

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x + y + 2)⁻¹ - (x + 1)⁻¹ * (y + 1)⁻¹ ≤ 16⁻¹ := by
  have h := (ShiftedReciprocalRange.source_bounds x y hx hy).2
  simpa only [ShiftedReciprocalRange.source_expression x y hx hy, one_div] using h

#print axioms ShiftedReciprocalRange.upper_gap
#print axioms ShiftedReciprocalRange.upper_bound
#print axioms ShiftedReciprocalRange.upper_equality
#print axioms ShiftedReciprocalRange.lower_gap
#print axioms ShiftedReciprocalRange.source_bounds
#print axioms ShiftedReciprocalRange.source_equality
#print axioms ShiftedReciprocalRange.diagonal_value
#print axioms ShiftedReciprocalRange.diagonal_preimage
#print axioms ShiftedReciprocalRange.range_classification
#print axioms ShiftedReciprocalRange.greatest_value
#print axioms ShiftedReciprocalRange.no_least
#print axioms ShiftedReciprocalRange.source_expression
#print axioms solution
