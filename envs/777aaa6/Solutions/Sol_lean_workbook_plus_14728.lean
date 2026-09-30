-- Prove2me | solution 1 for lean_workbook_plus_14728
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:25.550498+00:00
-- url     : https://prove2.me/submissions/8d7f356e-273a-49ae-bb7f-6c79f90983f6

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

namespace CenteredFourCycleExtrema

def value (x1 x2 x3 x4 a : ℝ) : ℝ :=
  (x1 - a) * (x2 - a) + (x2 - a) * (x3 - a) +
    (x3 - a) * (x4 - a) + (x4 - a) * (x1 - a)

def attainable (a : ℝ) : Set ℝ :=
  {v | ∃ x1 x2 x3 x4 : ℝ,
    a = (x1 + x2 + x3 + x4) / 4 ∧ value x1 x2 x3 x4 a = v}

theorem square_identity (x1 x2 x3 x4 a : ℝ)
    (h : a = (x1 + x2 + x3 + x4) / 4) :
    value x1 x2 x3 x4 a = -(x1 + x3 - 2 * a) ^ 2 := by
  unfold value
  linear_combination (-4 * (x1 + x3 - 2 * a)) * h

theorem sharp_bound (x1 x2 x3 x4 a : ℝ)
    (h : a = (x1 + x2 + x3 + x4) / 4) : value x1 x2 x3 x4 a ≤ 0 := by
  rw [square_identity x1 x2 x3 x4 a h]
  exact neg_nonpos.mpr (sq_nonneg _)

theorem equality_iff (x1 x2 x3 x4 a : ℝ)
    (h : a = (x1 + x2 + x3 + x4) / 4) :
    value x1 x2 x3 x4 a = 0 ↔ x1 + x3 = x2 + x4 := by
  rw [square_identity x1 x2 x3 x4 a h]
  constructor
  · intro hv
    have hs : (x1 + x3 - 2 * a) ^ 2 = 0 := by linarith
    have hz := sq_eq_zero_iff.mp hs
    linarith
  · intro he
    have hz : x1 + x3 - 2 * a = 0 := by linarith
    rw [hz]
    norm_num

theorem maximizing_family (a u v : ℝ) :
    a = ((a + u) + (a + v) + (a - u) + (a - v)) / 4 ∧
      value (a + u) (a + v) (a - u) (a - v) a = 0 := by
  constructor
  · ring
  · unfold value; ring

theorem maximizer_classification (x1 x2 x3 x4 a : ℝ) :
    (a = (x1 + x2 + x3 + x4) / 4 ∧ value x1 x2 x3 x4 a = 0) ↔
      ∃ u v : ℝ, x1 = a + u ∧ x2 = a + v ∧ x3 = a - u ∧ x4 = a - v := by
  constructor
  · rintro ⟨hm, hv⟩
    have he := (equality_iff x1 x2 x3 x4 a hm).mp hv
    refine ⟨x1 - a, x2 - a, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨u, v, rfl, rfl, rfl, rfl⟩
    exact maximizing_family a u v

theorem negative_square_model (a t : ℝ) :
    a = ((a + t) + (a - t) + a + a) / 4 ∧
      value (a + t) (a - t) a a a = -t ^ 2 := by
  constructor
  · ring
  · unfold value; ring

theorem level_attained (a v : ℝ) (hv : v ≤ 0) : v ∈ attainable a := by
  obtain ⟨hm, he⟩ := negative_square_model a (Real.sqrt (-v))
  refine ⟨a + Real.sqrt (-v), a - Real.sqrt (-v), a, a, hm, ?_⟩
  rw [he, Real.sq_sqrt (neg_nonneg.mpr hv), neg_neg]

theorem exact_range (a : ℝ) : attainable a = Set.Iic 0 := by
  ext v
  constructor
  · rintro ⟨x1, x2, x3, x4, hm, rfl⟩
    exact sharp_bound x1 x2 x3 x4 a hm
  · exact level_attained a v

theorem greatest_value (a : ℝ) : IsGreatest (attainable a) 0 := by
  rw [exact_range]
  constructor
  · simp
  · intro v hv
    exact hv

theorem unbounded_below (a L : ℝ) : ∃ v ∈ attainable a, v < L := by
  refine ⟨min L 0 - 1, level_attained a _ ?_, ?_⟩
  · have h := min_le_right L 0
    linarith
  · have h := min_le_left L 0
    linarith

theorem no_least_value (a : ℝ) : ¬ ∃ v : ℝ, IsLeast (attainable a) v := by
  rintro ⟨v, hv⟩
  obtain ⟨w, hw, hlt⟩ := unbounded_below a v
  exact (not_lt_of_ge (hv.2 hw)) hlt

end CenteredFourCycleExtrema

theorem solution (x1 x2 x3 x4 a : ℝ)
    (h1 : a = (x1 + x2 + x3 + x4) / 4) :
    (x1 - a) * (x2 - a) + (x2 - a) * (x3 - a) +
      (x3 - a) * (x4 - a) + (x4 - a) * (x1 - a) ≤ 0 := by
  exact CenteredFourCycleExtrema.sharp_bound x1 x2 x3 x4 a h1

#print axioms CenteredFourCycleExtrema.square_identity
#print axioms CenteredFourCycleExtrema.sharp_bound
#print axioms CenteredFourCycleExtrema.equality_iff
#print axioms CenteredFourCycleExtrema.maximizing_family
#print axioms CenteredFourCycleExtrema.maximizer_classification
#print axioms CenteredFourCycleExtrema.negative_square_model
#print axioms CenteredFourCycleExtrema.level_attained
#print axioms CenteredFourCycleExtrema.exact_range
#print axioms CenteredFourCycleExtrema.greatest_value
#print axioms CenteredFourCycleExtrema.unbounded_below
#print axioms CenteredFourCycleExtrema.no_least_value
#print axioms solution
