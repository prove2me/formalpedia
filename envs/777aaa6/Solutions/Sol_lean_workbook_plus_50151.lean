-- Prove2me | solution 1 for lean_workbook_plus_50151
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:25:38.60935+00:00
-- url     : https://prove2.me/submissions/7aaaada6-a076-4669-869a-03c4c0635ada

import Mathlib

namespace ReciprocalFourthPowerConstraint

noncomputable def pair (a b : ℝ) : ℝ := a / b + b / a

noncomputable def value (a b c : ℝ) : ℝ :=
  (a ^ 4 + b ^ 4 + c ^ 4) * (1 / a ^ 4 + 1 / b ^ 4 + 1 / c ^ 4)

theorem pair_lower {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 2 ≤ pair a b := by
  have hg : a * b * (pair a b - 2) = (a - b) ^ 2 := by
    unfold pair
    field_simp
    ring
  have hp := mul_pos ha hb
  nlinarith only [hg, hp, sq_nonneg (a - b)]

theorem pair_polynomial {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b * pair a b = a ^ 2 + b ^ 2 := by
  unfold pair
  field_simp

theorem constraint_identity {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a + b - c) * (1 / a + 1 / b - 1 / c) =
      3 + pair a b - pair a c - pair b c := by
  unfold pair
  field_simp
  ring

theorem trace_identity {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (pair a b) ^ 2 + (pair a c) ^ 2 + (pair b c) ^ 2 -
      pair a b * pair a c * pair b c = 4 := by
  unfold pair
  field_simp
  ring

theorem value_identity {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    value a b c = 9 + (pair a b) ^ 4 + (pair a c) ^ 4 + (pair b c) ^ 4 -
      4 * ((pair a b) ^ 2 + (pair a c) ^ 2 + (pair b c) ^ 2) := by
  unfold value pair
  field_simp
  ring

theorem scalar_lower {x y z : ℝ} (hy : 2 ≤ y) (hz : 2 ≤ z)
    (hl : x = y + z + 1) (ht : x ^ 2 + y ^ 2 + z ^ 2 - x * y * z = 4) :
    7 ≤ x := by
  have hx5 : 5 ≤ x := by linarith
  have hid : (x - 7) * (x - 2) * (x + 1) = (x + 2) * (y - z) ^ 2 := by
    rw [hl] at ht ⊢
    linear_combination -4 * ht
  have hn : 0 ≤ (x - 7) * (x - 2) * (x + 1) := by
    rw [hid]
    exact mul_nonneg (by linarith) (sq_nonneg (y - z))
  by_contra! hx
  have hneg := mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (show x - 7 < 0 by linarith) (show 0 < x - 2 by linarith))
    (show 0 < x + 1 by linarith)
  linarith

theorem scalar_gap_identity (x y z : ℝ) :
    9 + x ^ 4 + y ^ 4 + z ^ 4 - 4 * (x ^ 2 + y ^ 2 + z ^ 2) - 2304 =
      (x ^ 2 - 49) * (x ^ 2 + 45) + (y ^ 2 - z ^ 2) ^ 2 / 2 +
      (y ^ 2 + z ^ 2 - 18) * (y ^ 2 + z ^ 2 + 10) / 2 := by ring

theorem scalar_bound_equality {x y z : ℝ} (hy : 2 ≤ y) (hz : 2 ≤ z)
    (hl : x = y + z + 1) (ht : x ^ 2 + y ^ 2 + z ^ 2 - x * y * z = 4) :
    2304 ≤ 9 + x ^ 4 + y ^ 4 + z ^ 4 - 4 * (x ^ 2 + y ^ 2 + z ^ 2) ∧
      (9 + x ^ 4 + y ^ 4 + z ^ 4 - 4 * (x ^ 2 + y ^ 2 + z ^ 2) = 2304 ↔
        x = 7 ∧ y = 3 ∧ z = 3) := by
  have hx := scalar_lower hy hz hl ht
  have hsum : 6 ≤ y + z := by linarith
  have hs : 18 ≤ y ^ 2 + z ^ 2 := by
    nlinarith only [hsum, sq_nonneg (y - z)]
  have hx2 : 0 ≤ x ^ 2 - 49 := by nlinarith only [hx]
  have h1 := mul_nonneg hx2 (show 0 ≤ x ^ 2 + 45 by positivity)
  have h2 : 0 ≤ (y ^ 2 - z ^ 2) ^ 2 / 2 := by positivity
  have h3 := div_nonneg (mul_nonneg (show 0 ≤ y ^ 2 + z ^ 2 - 18 by linarith)
    (show 0 ≤ y ^ 2 + z ^ 2 + 10 by positivity)) (by norm_num : (0 : ℝ) ≤ 2)
  have hid := scalar_gap_identity x y z
  refine ⟨by linarith only [hid, h1, h2, h3], ?_⟩
  constructor
  · intro he
    have hzero : (x ^ 2 - 49) * (x ^ 2 + 45) = 0 := by
      linarith only [hid, he, h1, h2, h3]
    have hxzero := (mul_eq_zero.mp hzero).resolve_right
      (ne_of_gt (show 0 < x ^ 2 + 45 by positivity))
    have hx7 : x = 7 := by nlinarith only [hxzero, hx]
    have ht' := ht
    rw [hx7] at ht'
    have hsum6 : y + z = 6 := by linarith
    have hyz : y = z := by nlinarith only [ht', hsum6, sq_nonneg (y - z)]
    exact ⟨hx7, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

theorem source_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + b - c) * (1 / a + 1 / b - 1 / c) = 4) : 2304 ≤ value a b c := by
  have hi := constraint_identity (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)
  have hl : pair a b = pair a c + pair b c + 1 := by linarith
  rw [value_identity (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)]
  exact (scalar_bound_equality (pair_lower ha hc) (pair_lower hb hc) hl
    (trace_identity (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc))).1

theorem equality_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + b - c) * (1 / a + 1 / b - 1 / c) = 4) :
    value a b c = 2304 ↔ a * b = c ^ 2 ∧ a + b = 3 * c := by
  have ha0 := ne_of_gt ha
  have hb0 := ne_of_gt hb
  have hc0 := ne_of_gt hc
  have hi := constraint_identity ha0 hb0 hc0
  have hl : pair a b = pair a c + pair b c + 1 := by linarith
  have heq := (scalar_bound_equality (pair_lower ha hc) (pair_lower hb hc) hl
    (trace_identity ha0 hb0 hc0)).2
  rw [← value_identity ha0 hb0 hc0] at heq
  constructor
  · intro he
    obtain ⟨hx, hy, hz⟩ := heq.mp he
    have hxy := pair_polynomial ha0 hb0
    have hyc := pair_polynomial ha0 hc0
    have hzc := pair_polynomial hb0 hc0
    rw [hx] at hxy
    rw [hy] at hyc
    rw [hz] at hzc
    have habne : a ≠ b := by intro he; rw [he] at hxy; nlinarith only [hxy, hb]
    have hprod : (a - b) * (a * b - c ^ 2) = 0 := by
      linear_combination -b * hyc + a * hzc
    have hp : a * b = c ^ 2 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr habne))
    have hs : a * (a + b - 3 * c) = 0 := by linear_combination hp - hyc
    exact ⟨hp, by have := (mul_eq_zero.mp hs).resolve_left ha0; linarith⟩
  · rintro ⟨hp, hs⟩
    apply heq.mpr
    have hxy := pair_polynomial ha0 hb0
    have hyc := pair_polynomial ha0 hc0
    have hzc := pair_polynomial hb0 hc0
    have hya : a * c * (pair a c - 3) = 0 := by
      linear_combination hyc + a * hs - hp
    have hzb : b * c * (pair b c - 3) = 0 := by
      linear_combination hzc + b * hs - hp
    have hy : pair a c = 3 := sub_eq_zero.mp
      ((mul_eq_zero.mp hya).resolve_left (mul_ne_zero ha0 hc0))
    have hz : pair b c = 3 := sub_eq_zero.mp
      ((mul_eq_zero.mp hzb).resolve_left (mul_ne_zero hb0 hc0))
    exact ⟨by linarith, hy, hz⟩

theorem golden_model : ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    (a + b - c) * (1 / a + 1 / b - 1 / c) = 4 ∧ value a b c = 2304 := by
  let a : ℝ := (3 + Real.sqrt 5) / 2
  let b : ℝ := (3 - Real.sqrt 5) / 2
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg 5
  have hu : Real.sqrt 5 < 3 := by nlinarith only [hs, hn]
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; linarith
  have hab : a * b = 1 := by dsimp [a, b]; nlinarith only [hs]
  have hsum : a + b = 3 := by dsimp [a, b]; ring
  have hinv : 1 / a + 1 / b = 3 := by
    apply (mul_right_inj' (ne_of_gt (mul_pos ha hb))).mp
    calc
      _ = a + b := by field_simp; ring
      _ = (a * b) * 3 := by rw [hab, hsum]; ring
  have hh : (a + b - (1 : ℝ)) * (1 / a + 1 / b - 1 / 1) = 4 := by
    rw [hsum, hinv]
    norm_num
  refine ⟨a, b, 1, ha, hb, by norm_num, hh, ?_⟩
  exact (equality_iff ha hb (by norm_num) hh).mpr ⟨by simpa using hab, by simpa using hsum⟩

theorem sharp_lower_constant (k : ℝ) :
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
      (a + b - c) * (1 / a + 1 / b - 1 / c) = 4 → k ≤ value a b c) ↔ k ≤ 2304 := by
  constructor
  · intro h
    obtain ⟨a, b, c, ha, hb, hc, hh, he⟩ := golden_model
    simpa only [he] using h a b c ha hb hc hh
  · intro hk a b c ha hb hc hh
    exact hk.trans (source_bound ha hb hc hh)

end ReciprocalFourthPowerConstraint

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_hab : a + b > c) (_hbc : b + c > a) (_hca : a + c > b)
    (h : (a + b - c) * (1 / a + 1 / b - 1 / c) = 4) :
    (a ^ 4 + b ^ 4 + c ^ 4) * (1 / a ^ 4 + 1 / b ^ 4 + 1 / c ^ 4) ≥ 2304 :=
  ReciprocalFourthPowerConstraint.source_bound ha hb hc h

#print axioms ReciprocalFourthPowerConstraint.pair
#print axioms ReciprocalFourthPowerConstraint.value
#print axioms ReciprocalFourthPowerConstraint.pair_lower
#print axioms ReciprocalFourthPowerConstraint.pair_polynomial
#print axioms ReciprocalFourthPowerConstraint.constraint_identity
#print axioms ReciprocalFourthPowerConstraint.trace_identity
#print axioms ReciprocalFourthPowerConstraint.value_identity
#print axioms ReciprocalFourthPowerConstraint.scalar_lower
#print axioms ReciprocalFourthPowerConstraint.scalar_gap_identity
#print axioms ReciprocalFourthPowerConstraint.scalar_bound_equality
#print axioms ReciprocalFourthPowerConstraint.source_bound
#print axioms ReciprocalFourthPowerConstraint.equality_iff
#print axioms ReciprocalFourthPowerConstraint.golden_model
#print axioms ReciprocalFourthPowerConstraint.sharp_lower_constant
#print axioms solution
