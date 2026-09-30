-- Prove2me | solution 1 for lean_workbook_plus_17637
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:44:54.126385+00:00
-- url     : https://prove2.me/submissions/dbbd0d9f-fbfa-4570-b8d3-d0b61b37d822

import Mathlib

namespace AbsoluteDeviationMinimizers

noncomputable def value (x y : ℝ) : ℝ :=
  |x - 1| + |x - 2| + |x - 3| + |x - 4| + |y - 1| + |y - 2| + |y - 3|

theorem pair_lower_bound (a b t : ℝ) : b - a ≤ |t - a| + |t - b| := by
  have ha := le_abs_self (t - a)
  have hb := neg_abs_le (t - b)
  linarith only [ha, hb]

theorem pair_equality_iff (a b t : ℝ) :
    |t - a| + |t - b| = b - a ↔ a ≤ t ∧ t ≤ b := by
  constructor
  · intro he
    have ha := le_abs_self (t - a)
    have hb := neg_abs_le (t - b)
    have hna := abs_nonneg (t - a)
    have hnb := abs_nonneg (t - b)
    constructor <;> linarith only [he, ha, hb, hna, hnb]
  · rintro ⟨ha, hb⟩
    rw [abs_of_nonneg (sub_nonneg.mpr ha), abs_of_nonpos (sub_nonpos.mpr hb)]
    ring

theorem lower_bound (x y : ℝ) : 6 ≤ value x y := by
  have h14 := pair_lower_bound 1 4 x
  have h23 := pair_lower_bound 2 3 x
  have h13 := pair_lower_bound 1 3 y
  have hy := abs_nonneg (y - 2)
  unfold value
  linarith only [h14, h23, h13, hy]

theorem equality_iff (x y : ℝ) : value x y = 6 ↔ 2 ≤ x ∧ x ≤ 3 ∧ y = 2 := by
  constructor
  · intro he
    have h14 := pair_lower_bound 1 4 x
    have h23 := pair_lower_bound 2 3 x
    have h13 := pair_lower_bound 1 3 y
    have hy := abs_nonneg (y - 2)
    unfold value at he
    have hm : |x - 2| + |x - 3| = 3 - 2 := by linarith only [he, h14, h23, h13, hy]
    have hz : |y - 2| = 0 := by linarith only [he, h14, h23, h13, hy]
    obtain ⟨hx2, hx3⟩ := (pair_equality_iff 2 3 x).mp hm
    exact ⟨hx2, hx3, sub_eq_zero.mp (abs_eq_zero.mp hz)⟩
  · rintro ⟨hx2, hx3, rfl⟩
    have h14 := (pair_equality_iff 1 4 x).mpr ⟨by linarith, by linarith⟩
    have h23 := (pair_equality_iff 2 3 x).mpr ⟨hx2, hx3⟩
    have h13 := (pair_equality_iff 1 3 2).mpr ⟨by norm_num, by norm_num⟩
    have hy : |(2 : ℝ) - 2| = 0 := by simp
    unfold value
    linarith only [h14, h23, h13, hy]

theorem genuine_model : value 2 2 = 6 :=
  (equality_iff 2 2).mpr ⟨le_rfl, by norm_num, rfl⟩

theorem minimum : IsLeast (Set.range (fun p : ℝ × ℝ => value p.1 p.2)) 6 := by
  refine ⟨⟨(2, 2), genuine_model⟩, ?_⟩
  rintro v ⟨p, rfl⟩
  exact lower_bound p.1 p.2

theorem minimizer_set :
    {p : ℝ × ℝ | value p.1 p.2 = 6} = {p : ℝ × ℝ | 2 ≤ p.1 ∧ p.1 ≤ 3 ∧ p.2 = 2} := by
  ext p
  exact equality_iff p.1 p.2

end AbsoluteDeviationMinimizers

theorem solution (x y : ℝ) :
    6 ≤ abs (x - 1) + abs (x - 2) + abs (x - 3) + abs (x - 4) +
      abs (y - 1) + abs (y - 2) + abs (y - 3) := by
  exact AbsoluteDeviationMinimizers.lower_bound x y

#print axioms AbsoluteDeviationMinimizers.pair_lower_bound
#print axioms AbsoluteDeviationMinimizers.pair_equality_iff
#print axioms AbsoluteDeviationMinimizers.lower_bound
#print axioms AbsoluteDeviationMinimizers.equality_iff
#print axioms AbsoluteDeviationMinimizers.genuine_model
#print axioms AbsoluteDeviationMinimizers.minimum
#print axioms AbsoluteDeviationMinimizers.minimizer_set
#print axioms solution
