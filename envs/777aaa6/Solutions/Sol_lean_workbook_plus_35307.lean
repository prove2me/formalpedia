-- Prove2me | solution 1 for lean_workbook_plus_35307
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:46:06.940671+00:00
-- url     : https://prove2.me/submissions/c892d716-3223-428c-9e12-0ccea44c7e24

import Mathlib

namespace ReciprocalCubicSharpMaximum

def System (x y : ℝ) : Prop := 0 < x ∧ 0 < y ∧ (x + y + 1) * x * y = x ^ 2 + y ^ 2

noncomputable def value (x y : ℝ) : ℝ := 1 / x ^ 3 + 1 / y ^ 3

def attainable : Set ℝ := {P | ∃ x y : ℝ, System x y ∧ value x y = P}

theorem reciprocal_equivalence (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x + y + 1) * x * y = x ^ 2 + y ^ 2 ↔
      (1 / x) ^ 2 + (1 / y) ^ 2 = 1 / x + 1 / y + (1 / x) * (1 / y) := by
  constructor
  · intro h
    field_simp [hx, hy]
    nlinarith only [h]
  · intro h
    field_simp [hx, hy] at h
    nlinarith only [h]

theorem scalar_data (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (h : u ^ 2 + v ^ 2 = u + v + u * v) :
    1 < u + v ∧ u + v ≤ 4 ∧ u ^ 3 + v ^ 3 = (u + v) ^ 2 := by
  have hp : (u + v) ^ 2 - (u + v) = 3 * u * v := by nlinarith only [h]
  have hg : (u + v) * (4 - (u + v)) = 3 * (u - v) ^ 2 := by nlinarith only [h]
  refine ⟨?_, ?_, ?_⟩
  · by_contra hn
    have hm := mul_nonneg (le_of_lt (add_pos hu hv)) (show 0 ≤ 1 - (u + v) by linarith)
    have huv := mul_pos hu hv
    nlinarith only [hp, hm, huv]
  · by_contra hn
    have hm := mul_pos (add_pos hu hv) (show 0 < u + v - 4 by linarith)
    nlinarith only [hg, hm, sq_nonneg (u - v)]
  · linear_combination (u + v) * h

theorem scalar_bounds (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (h : u ^ 2 + v ^ 2 = u + v + u * v) :
    1 < u ^ 3 + v ^ 3 ∧ u ^ 3 + v ^ 3 ≤ 16 := by
  obtain ⟨hl, hh, he⟩ := scalar_data u v hu hv h
  have hlow := mul_pos (sub_pos.mpr hl) (show 0 < u + v + 1 by linarith)
  have hhigh := mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ 4 + (u + v) by linarith)
  constructor <;> nlinarith only [he, hlow, hhigh]

theorem scalar_equality (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (h : u ^ 2 + v ^ 2 = u + v + u * v) :
    u ^ 3 + v ^ 3 = 16 ↔ u = 2 ∧ v = 2 := by
  obtain ⟨hl, _, hi⟩ := scalar_data u v hu hv h
  constructor
  · intro he
    have hs : u + v = 4 := by
      apply (sq_eq_sq₀ (by linarith : 0 ≤ u + v) (by norm_num : (0 : ℝ) ≤ 4)).mp
      nlinarith only [hi, he]
    have hg : (u + v) * (4 - (u + v)) = 3 * (u - v) ^ 2 := by nlinarith only [h]
    rw [hs] at hg
    have hz : (u - v) ^ 2 = 0 := by nlinarith only [hg]
    have heq := sq_eq_zero_iff.mp hz
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    ring

theorem source_bounds (x y : ℝ) (h : System x y) : 1 < value x y ∧ value x y ≤ 16 := by
  obtain ⟨hx, hy, he⟩ := h
  have hr := (reciprocal_equivalence x y (ne_of_gt hx) (ne_of_gt hy)).mp he
  have hb := scalar_bounds (1 / x) (1 / y) (by positivity) (by positivity) hr
  simpa only [value, div_pow, one_pow] using hb

theorem genuine_model : System (1 / 2) (1 / 2) ∧ value (1 / 2) (1 / 2) = 16 := by
  refine ⟨⟨by norm_num, by norm_num, by ring⟩, ?_⟩
  unfold value
  ring

theorem equality_iff (x y : ℝ) (h : System x y) :
    value x y = 16 ↔ x = 1 / 2 ∧ y = 1 / 2 := by
  obtain ⟨hx, hy, he⟩ := h
  have hr := (reciprocal_equivalence x y (ne_of_gt hx) (ne_of_gt hy)).mp he
  constructor
  · intro hm
    have hh : (1 / x) ^ 3 + (1 / y) ^ 3 = 16 := by
      simpa only [value, div_pow, one_pow] using hm
    obtain ⟨hx', hy'⟩ :=
      (scalar_equality (1 / x) (1 / y) (by positivity) (by positivity) hr).mp hh
    have hxx := (div_eq_iff (ne_of_gt hx)).mp hx'
    have hyy := (div_eq_iff (ne_of_gt hy)).mp hy'
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    exact genuine_model.2

theorem maximum : IsGreatest attainable 16 := by
  refine ⟨⟨1 / 2, 1 / 2, genuine_model⟩, ?_⟩
  rintro P ⟨x, y, h, hv⟩
  rw [← hv]
  exact (source_bounds x y h).2

end ReciprocalCubicSharpMaximum

theorem solution (x y P : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hP : P = 1 / x ^ 3 + 1 / y ^ 3) (h : (x + y + 1) * x * y = x ^ 2 + y ^ 2) :
    P ≤ 16 := by
  rw [hP]
  exact (ReciprocalCubicSharpMaximum.source_bounds x y ⟨hx, hy, h⟩).2

#print axioms ReciprocalCubicSharpMaximum.reciprocal_equivalence
#print axioms ReciprocalCubicSharpMaximum.scalar_data
#print axioms ReciprocalCubicSharpMaximum.scalar_bounds
#print axioms ReciprocalCubicSharpMaximum.scalar_equality
#print axioms ReciprocalCubicSharpMaximum.source_bounds
#print axioms ReciprocalCubicSharpMaximum.genuine_model
#print axioms ReciprocalCubicSharpMaximum.equality_iff
#print axioms ReciprocalCubicSharpMaximum.maximum
#print axioms solution
