-- Prove2me | solution 1 for lean_workbook_plus_54891
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:00:38.828889+00:00
-- url     : https://prove2.me/submissions/daaf1dee-2850-4663-be0a-f09f78eeaefd

import Mathlib

namespace AffineQuadraticExactRange

def value (x y : ℝ) : ℝ := x ^ 2 - 5 * x + y ^ 2 + x * y - 4 * y + 2014

theorem gap_identity (x y : ℝ) :
    4 * (value x y - 2007) = (2 * x + y - 5) ^ 2 + 3 * (y - 1) ^ 2 := by
  unfold value
  ring

theorem sharp_bound (x y : ℝ) : 2007 ≤ value x y := by
  nlinarith [gap_identity x y, sq_nonneg (2 * x + y - 5), sq_nonneg (y - 1)]

theorem unique_minimizer (x y : ℝ) : value x y = 2007 ↔ x = 2 ∧ y = 1 := by
  constructor
  · intro h
    have hs : (y - 1) ^ 2 = 0 := by
      nlinarith [gap_identity x y, sq_nonneg (2 * x + y - 5), sq_nonneg (y - 1)]
    have hy : y = 1 := by nlinarith
    have hx : x = 2 := by
      subst y
      unfold value at h
      nlinarith [sq_nonneg (x - 2)]
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    unfold value
    ring

theorem exact_range :
    Set.range (fun p : ℝ × ℝ => value p.1 p.2) = Set.Ici 2007 := by
  ext r
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    exact sharp_bound x y
  · intro hr
    have hs := Real.sq_sqrt (sub_nonneg.mpr hr)
    refine ⟨(2 + Real.sqrt (r - 2007), 1), ?_⟩
    change value (2 + Real.sqrt (r - 2007)) 1 = r
    unfold value
    nlinarith

theorem distance_control (x y : ℝ) :
    (x - 2) ^ 2 + (y - 1) ^ 2 ≤ 2 * (value x y - 2007) := by
  unfold value
  nlinarith [sq_nonneg (x + y - 3)]

end AffineQuadraticExactRange

theorem solution (x y : ℝ) : x ^ 2 - 5 * x + y ^ 2 + x * y - 4 * y + 2014 ≥ -1879 := by
  have h := AffineQuadraticExactRange.sharp_bound x y
  unfold AffineQuadraticExactRange.value at h
  linarith

#print axioms AffineQuadraticExactRange.gap_identity
#print axioms AffineQuadraticExactRange.sharp_bound
#print axioms AffineQuadraticExactRange.unique_minimizer
#print axioms AffineQuadraticExactRange.exact_range
#print axioms AffineQuadraticExactRange.distance_control
#print axioms solution
