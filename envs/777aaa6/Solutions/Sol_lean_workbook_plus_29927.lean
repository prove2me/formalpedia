-- Prove2me | solution 1 for lean_workbook_plus_29927
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:14:32.475897+00:00
-- url     : https://prove2.me/submissions/3b83d67f-aae4-4c29-8429-276483cc20f9

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace CyclicIntegerReciprocalBounds

def leftValue (x y z : ℝ) : ℝ :=
  x / (z * x + 2 * x + 1) + y / (x * y + 2 * y + 1) +
    z / (y * z + 2 * z + 1)

def rightValue (x y z : ℝ) : ℝ :=
  x / (x * y + 2 * y + 1) + y / (y * z + 2 * z + 1) +
    z / (z * x + 2 * x + 1)

def denominator (x y z : ℝ) : ℝ :=
  (z * x + 2 * x + 1) * (x * y + 2 * y + 1) * (y * z + 2 * z + 1)

def leftGap (a b c : ℝ) : ℝ :=
  8 * (a ^ 2 + b ^ 2 + c ^ 2) + 8 * (a * b + b * c + c * a) +
    11 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) +
    13 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) + 24 * a * b * c +
    5 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) +
    19 * a * b * c * (a + b + c) + 8 * a * b * c * (a * b + b * c + c * a) +
    3 * a ^ 2 * b ^ 2 * c ^ 2

def rightGap (a b c : ℝ) : ℝ :=
  128 + 128 * (a + b + c) + 176 * (a * b + b * c + c * a) +
    9 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) +
    39 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) + 272 * a * b * c +
    3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) +
    61 * a * b * c * (a + b + c) + 16 * a * b * c * (a * b + b * c + c * a) +
    5 * a ^ 2 * b ^ 2 * c ^ 2

theorem denominator_pos (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 < denominator x y z := by
  dsimp [denominator]
  positivity

theorem left_gap_identity (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (3 / 4 - leftValue x y z) * (4 * denominator x y z) =
      leftGap (x - 1) (y - 1) (z - 1) := by
  have h1 : z * x + 2 * x + 1 ≠ 0 := ne_of_gt (by positivity)
  have h2 : x * y + 2 * y + 1 ≠ 0 := ne_of_gt (by positivity)
  have h3 : y * z + 2 * z + 1 ≠ 0 := ne_of_gt (by positivity)
  dsimp [leftValue, denominator, leftGap]
  field_simp
  ring

theorem right_gap_identity (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (5 / 4 - rightValue x y z) * (4 * denominator x y z) =
      rightGap (x - 1) (y - 1) (z - 1) := by
  have h1 : z * x + 2 * x + 1 ≠ 0 := ne_of_gt (by positivity)
  have h2 : x * y + 2 * y + 1 ≠ 0 := ne_of_gt (by positivity)
  have h3 : y * z + 2 * z + 1 ≠ 0 := ne_of_gt (by positivity)
  dsimp [rightValue, denominator, rightGap]
  field_simp
  ring

theorem left_gap_lower (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    8 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ leftGap a b c := by
  have h : 0 ≤ leftGap a b c - 8 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    dsimp [leftGap]
    ring_nf
    positivity
  linarith only [h]

theorem right_gap_pos (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 < rightGap a b c := by
  dsimp [rightGap]
  positivity

theorem left_bounds (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    0 < leftValue x y z ∧ leftValue x y z ≤ 3 / 4 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  refine ⟨by dsimp [leftValue]; positivity, ?_⟩
  have hg := left_gap_lower (x - 1) (y - 1) (z - 1)
    (by linarith) (by linarith) (by linarith)
  have hi := left_gap_identity x y z hx0.le hy0.le hz0.le
  have hd := denominator_pos x y z hx0.le hy0.le hz0.le
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]

theorem left_equality (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    leftValue x y z = 3 / 4 ↔ x = 1 ∧ y = 1 ∧ z = 1 := by
  constructor
  · intro he
    have hg := left_gap_lower (x - 1) (y - 1) (z - 1)
      (by linarith) (by linarith) (by linarith)
    have hi := left_gap_identity x y z (by linarith) (by linarith) (by linarith)
    rw [he] at hi
    simp only [sub_self, zero_mul] at hi
    rw [← hi] at hg
    have hs : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 = 0 := by
      linarith only [hg, sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have hx' : (x - 1) ^ 2 = 0 := by linarith only [hs, sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have hy' : (y - 1) ^ 2 = 0 := by linarith only [hs, sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have hz' : (z - 1) ^ 2 = 0 := by linarith only [hs, sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    exact ⟨by nlinarith [sq_eq_zero_iff.mp hx'],
      by nlinarith [sq_eq_zero_iff.mp hy'], by nlinarith [sq_eq_zero_iff.mp hz']⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num [leftValue]

theorem right_bounds (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    0 < rightValue x y z ∧ rightValue x y z < 5 / 4 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  refine ⟨by dsimp [rightValue]; positivity, ?_⟩
  have hg := right_gap_pos (x - 1) (y - 1) (z - 1)
    (by linarith) (by linarith) (by linarith)
  have hi := right_gap_identity x y z hx0.le hy0.le hz0.le
  have hd := denominator_pos x y z hx0.le hy0.le hz0.le
  nlinarith

theorem diagonal (t : ℝ) :
    leftValue t t t = 3 * t / (t + 1) ^ 2 ∧
      rightValue t t t = 3 * t / (t + 1) ^ 2 := by
  have he : t * t + 2 * t + 1 = (t + 1) ^ 2 := by ring
  simp only [leftValue, rightValue, he]
  constructor <;> ring

theorem edge_family (t : ℝ) :
    rightValue t 1 1 = t / (t + 3) + 1 / 4 + 1 / (3 * t + 1) := by
  simp only [rightValue]
  congr 2 <;> congr 1 <;> ring

theorem diagonal_small (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ leftValue n n n < ε ∧ rightValue n n n < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / ε + 1)
  have hn1 : 1 < (n : ℝ) := by
    have : 0 < 3 / ε := by positivity
    linarith
  have hn0 : 0 < n := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hn1)
  have hmul : 3 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp (by linarith : 3 / ε < n)
  have hsq : (n : ℝ) ^ 2 < ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hden : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  have hsmall : 3 * (n : ℝ) / ((n : ℝ) + 1) ^ 2 < ε := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_pos (by linarith : 0 < (n : ℝ)) (by linarith : 0 < (n : ℝ) * ε - 3),
      mul_pos hε (by linarith : 0 < ((n : ℝ) + 1) ^ 2 - (n : ℝ) ^ 2)]
  exact ⟨n, hn0, (diagonal n).1 ▸ hsmall, (diagonal n).2 ▸ hsmall⟩

theorem near_right_supremum (K : ℝ) (hK : K < 5 / 4) :
    ∃ n : ℕ, 0 < n ∧ K < rightValue n 1 1 := by
  have hg : 0 < 5 / 4 - K := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / (5 / 4 - K) + 1)
  have hn1 : 1 < (n : ℝ) := by
    have : 0 < 3 / (5 / 4 - K) := by positivity
    linarith
  have hn0 : 0 < n := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hn1)
  have hm : 3 < (n : ℝ) * (5 / 4 - K) :=
    (div_lt_iff₀ hg).mp (by linarith : 3 / (5 / 4 - K) < n)
  have hf : K - 1 / 4 < (n : ℝ) / ((n : ℝ) + 3) := by
    apply (lt_div_iff₀ (by linarith : 0 < (n : ℝ) + 3)).mpr
    nlinarith
  refine ⟨n, hn0, ?_⟩
  rw [edge_family]
  have : 0 < (1 : ℝ) / (3 * (n : ℝ) + 1) := by positivity
  linarith

theorem left_upper_constants (K : ℝ) :
    (∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → leftValue x y z ≤ K) ↔ 3 / 4 ≤ K := by
  constructor
  · intro h
    have hh := h 1 1 1 (by decide) (by decide) (by decide)
    norm_num [leftValue] at hh
    exact hh
  · intro h x y z hx hy hz
    exact (left_bounds x y z (by exact_mod_cast hx) (by exact_mod_cast hy)
      (by exact_mod_cast hz)).2.trans h

theorem right_upper_constants (K : ℝ) :
    (∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → rightValue x y z ≤ K) ↔ 5 / 4 ≤ K := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨n, hn0, hv⟩ := near_right_supremum K (lt_of_not_ge hn)
    have hh := h n 1 1 hn0 (by decide) (by decide)
    norm_num only [Nat.cast_one] at hh
    exact (not_lt_of_ge hh) hv
  · intro h x y z hx hy hz
    exact (right_bounds x y z (by exact_mod_cast hx) (by exact_mod_cast hy)
      (by exact_mod_cast hz)).2.le.trans h

theorem lower_constants (K : ℝ) :
    ((∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → K ≤ leftValue x y z) ↔ K ≤ 0) ∧
    ((∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → K ≤ rightValue x y z) ↔ K ≤ 0) := by
  constructor <;> constructor
  · intro h
    by_contra hn
    obtain ⟨n, hn0, hl, _⟩ := diagonal_small K (lt_of_not_ge hn)
    exact (not_lt_of_ge (h n n n hn0 hn0 hn0)) hl
  · intro h x y z hx hy hz
    exact h.trans (left_bounds x y z (by exact_mod_cast hx) (by exact_mod_cast hy)
      (by exact_mod_cast hz)).1.le
  · intro h
    by_contra hn
    obtain ⟨n, hn0, _, hr⟩ := diagonal_small K (lt_of_not_ge hn)
    exact (not_lt_of_ge (h n n n hn0 hn0 hn0)) hr
  · intro h x y z hx hy hz
    exact h.trans (right_bounds x y z (by exact_mod_cast hx) (by exact_mod_cast hy)
      (by exact_mod_cast hz)).1.le

theorem source_counterfamily (n : ℕ) (hn : 2 ≤ n) :
    ¬ (leftValue n n n ≤ 3 / 4 ∧ 3 / 4 ≤ rightValue n n n) := by
  intro h
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  rw [(diagonal n).2] at h
  have he := (le_div_iff₀ hd).mp h.2
  nlinarith [sq_nonneg ((n : ℝ) - 2)]

theorem left_cyclic (x y z : ℝ) : leftValue x y z = leftValue y z x := by
  unfold leftValue
  ring

theorem zero_coordinate_bound (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    leftValue 0 y z < 2 / 3 := by
  have h1 : 0 < 2 * y + 1 := by positivity
  have h2 : 0 < y * z + 2 * z + 1 := by positivity
  have hi : (2 / 3 - leftValue 0 y z) * (3 * (2 * y + 1) * (y * z + 2 * z + 1)) =
      (y - 1) ^ 2 * z + y + 2 := by
    dsimp [leftValue]
    field_simp
    ring
  have hp : 0 < (y - 1) ^ 2 * z + y + 2 := by positivity
  have hd : 0 < 3 * (2 * y + 1) * (y * z + 2 * z + 1) := by positivity
  nlinarith only [hi, hp, hd]

theorem nonnegative_integer_left_bound (x y z : ℕ) :
    0 ≤ leftValue x y z ∧ leftValue x y z ≤ 3 / 4 := by
  refine ⟨by dsimp [leftValue]; positivity, ?_⟩
  by_cases hx : x = 0
  · subst x
    have h := zero_coordinate_bound y z (by positivity) (by positivity)
    norm_num only [Nat.cast_zero]
    linarith only [h]
  by_cases hy : y = 0
  · subst y
    rw [left_cyclic]
    have h := zero_coordinate_bound z x (by positivity) (by positivity)
    norm_num only [Nat.cast_zero]
    linarith only [h]
  by_cases hz : z = 0
  · subst z
    rw [left_cyclic, left_cyclic (y : ℝ)]
    have h := zero_coordinate_bound x y (by positivity) (by positivity)
    norm_num only [Nat.cast_zero]
    linarith only [h]
  exact (left_bounds x y z (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx)
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hy)
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz)).2

theorem nonnegative_integer_left_equality (x y z : ℕ) :
    leftValue x y z = 3 / 4 ↔ x = 1 ∧ y = 1 ∧ z = 1 := by
  constructor
  · intro he
    have hx : x ≠ 0 := by
      intro h
      subst x
      have h := zero_coordinate_bound y z (by positivity) (by positivity)
      norm_num only [Nat.cast_zero] at he
      linarith only [he, h]
    have hy : y ≠ 0 := by
      intro h
      subst y
      rw [left_cyclic] at he
      have h := zero_coordinate_bound z x (by positivity) (by positivity)
      norm_num only [Nat.cast_zero] at he
      linarith only [he, h]
    have hz : z ≠ 0 := by
      intro h
      subst z
      rw [left_cyclic, left_cyclic (y : ℝ)] at he
      have h := zero_coordinate_bound x y (by positivity) (by positivity)
      norm_num only [Nat.cast_zero] at he
      linarith only [he, h]
    have h := (left_equality x y z (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hy)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz)).mp he
    exact_mod_cast h
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num [leftValue]

theorem zero_axis_right (x : ℝ) : rightValue x 0 0 = x := by
  simp [rightValue]

theorem nonnegative_integer_right_unbounded (K : ℝ) :
    ∃ n : ℕ, K < rightValue n 0 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt K
  exact ⟨n, by simpa [zero_axis_right] using hn⟩

theorem natural_quotient_zero (x z : ℕ) : x / (z * x + 2 * x + 1) = 0 := by
  apply Nat.div_eq_of_lt
  omega

end CyclicIntegerReciprocalBounds

theorem solution (x y z : ℕ) :
    (x / (z * x + 2 * x + 1) + y / (x * y + 2 * y + 1) +
      z / (y * z + 2 * z + 1) ≤ 3 / 4 ∧
    3 / 4 ≤ x / (x * y + 2 * y + 1) + y / (y * z + 2 * z + 1) +
      z / (z * x + 2 * x + 1)) := by
  simp [CyclicIntegerReciprocalBounds.natural_quotient_zero]

#print axioms CyclicIntegerReciprocalBounds.leftValue
#print axioms CyclicIntegerReciprocalBounds.rightValue
#print axioms CyclicIntegerReciprocalBounds.denominator
#print axioms CyclicIntegerReciprocalBounds.leftGap
#print axioms CyclicIntegerReciprocalBounds.rightGap
#print axioms CyclicIntegerReciprocalBounds.denominator_pos
#print axioms CyclicIntegerReciprocalBounds.left_gap_identity
#print axioms CyclicIntegerReciprocalBounds.right_gap_identity
#print axioms CyclicIntegerReciprocalBounds.left_gap_lower
#print axioms CyclicIntegerReciprocalBounds.right_gap_pos
#print axioms CyclicIntegerReciprocalBounds.left_bounds
#print axioms CyclicIntegerReciprocalBounds.left_equality
#print axioms CyclicIntegerReciprocalBounds.right_bounds
#print axioms CyclicIntegerReciprocalBounds.diagonal
#print axioms CyclicIntegerReciprocalBounds.edge_family
#print axioms CyclicIntegerReciprocalBounds.diagonal_small
#print axioms CyclicIntegerReciprocalBounds.near_right_supremum
#print axioms CyclicIntegerReciprocalBounds.left_upper_constants
#print axioms CyclicIntegerReciprocalBounds.right_upper_constants
#print axioms CyclicIntegerReciprocalBounds.lower_constants
#print axioms CyclicIntegerReciprocalBounds.source_counterfamily
#print axioms CyclicIntegerReciprocalBounds.left_cyclic
#print axioms CyclicIntegerReciprocalBounds.zero_coordinate_bound
#print axioms CyclicIntegerReciprocalBounds.nonnegative_integer_left_bound
#print axioms CyclicIntegerReciprocalBounds.nonnegative_integer_left_equality
#print axioms CyclicIntegerReciprocalBounds.zero_axis_right
#print axioms CyclicIntegerReciprocalBounds.nonnegative_integer_right_unbounded
#print axioms CyclicIntegerReciprocalBounds.natural_quotient_zero
#print axioms solution
