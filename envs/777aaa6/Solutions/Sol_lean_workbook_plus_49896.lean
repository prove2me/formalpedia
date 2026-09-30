-- Prove2me | solution 1 for lean_workbook_plus_49896
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:25:15.125936+00:00
-- url     : https://prove2.me/submissions/6158690d-4749-4fa2-9d46-200493d93fdf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace AbsoluteAffineSublevel

def value (x : ℝ) : ℝ := |4 * x + 3| - |x + 5|

theorem left_piece (x : ℝ) (hx : x ≤ -5) : value x = -3 * x + 2 := by
  have h4 : 4 * x + 3 ≤ 0 := by linarith
  have h1 : x + 5 ≤ 0 := by linarith
  unfold value
  rw [abs_of_nonpos h4, abs_of_nonpos h1]
  ring

theorem middle_piece (x : ℝ) (hx : -5 ≤ x) (hy : x ≤ -3 / 4) :
    value x = -5 * x - 8 := by
  have h4 : 4 * x + 3 ≤ 0 := by linarith
  have h1 : 0 ≤ x + 5 := by linarith
  unfold value
  rw [abs_of_nonpos h4, abs_of_nonneg h1]
  ring

theorem right_piece (x : ℝ) (hx : -3 / 4 ≤ x) : value x = 3 * x - 2 := by
  have h4 : 0 ≤ 4 * x + 3 := by linarith
  have h1 : 0 ≤ x + 5 := by linarith
  unfold value
  rw [abs_of_nonneg h4, abs_of_nonneg h1]
  ring

theorem sublevel_classification (x v : ℝ) :
    value x ≤ v ↔ -17 / 4 ≤ v ∧
      (if v ≤ 17 then -(v + 8) / 5 else (2 - v) / 3) ≤ x ∧ x ≤ (v + 2) / 3 := by
  unfold value
  split_ifs with hv <;>
    rcases le_total (4 * x + 3) 0 with h4 | h4 <;>
    rcases le_total (x + 5) 0 with h1 | h1 <;>
    simp_all only [abs_of_nonpos, abs_of_nonneg]
  all_goals
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩ <;> linarith
    · rintro ⟨h0, hlow, hupp⟩
      linarith

theorem minimum_equality (x : ℝ) : value x = -17 / 4 ↔ x = -3 / 4 := by
  constructor
  · intro h
    have he := (sublevel_classification x (-17 / 4)).mp (le_of_eq h)
    norm_num at he
    linarith [he.1, he.2]
  · rintro rfl
    norm_num [value]

theorem lower_bound (x : ℝ) : -17 / 4 ≤ value x := by
  exact ((sublevel_classification x (value x)).mp le_rfl).1

theorem exact_range : Set.range value = Set.Ici (-17 / 4) := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact lower_bound x
  · intro hv
    refine ⟨(v + 2) / 3, ?_⟩
    have hx : -3 / 4 ≤ (v + 2) / 3 := by
      change -17 / 4 ≤ v at hv
      linarith
    rw [right_piece _ hx]
    ring

theorem source_solution_set : {x : ℝ | value x ≤ 8} = Set.Icc (-16 / 5) (10 / 3) := by
  ext x
  simp only [Set.mem_setOf_eq, sublevel_classification, Set.mem_Icc]
  norm_num

theorem boundary_values : value (-16 / 5) = 8 ∧ value (10 / 3) = 8 := by
  constructor
  · rw [middle_piece _ (by norm_num) (by norm_num)]
    ring
  · rw [right_piece _ (by norm_num)]
    ring

end AbsoluteAffineSublevel

theorem solution (x : ℝ) : |4 * x + 3| - |x + 5| ≤ 8 ↔
    -16 / 5 ≤ x ∧ x ≤ 10 / 3 := by
  have h := AbsoluteAffineSublevel.sublevel_classification x 8
  norm_num [AbsoluteAffineSublevel.value] at h
  simpa [sub_le_iff_le_add, neg_div] using h

#print axioms AbsoluteAffineSublevel.left_piece
#print axioms AbsoluteAffineSublevel.middle_piece
#print axioms AbsoluteAffineSublevel.right_piece
#print axioms AbsoluteAffineSublevel.sublevel_classification
#print axioms AbsoluteAffineSublevel.minimum_equality
#print axioms AbsoluteAffineSublevel.lower_bound
#print axioms AbsoluteAffineSublevel.exact_range
#print axioms AbsoluteAffineSublevel.source_solution_set
#print axioms AbsoluteAffineSublevel.boundary_values
#print axioms solution
