-- Prove2me | solution 1 for lean_workbook_plus_32180
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:21:08.201116+00:00
-- url     : https://prove2.me/submissions/bc57665d-a989-49fe-aa8d-aacffa65ff9c

import Mathlib

set_option autoImplicit false

theorem update_bounds (t : Real) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < t*(1-t)*(1+t^2) ∧ t*(1-t)*(1+t^2) < t := by
  have hq : 0 < 1-t+t^2 := by nlinarith [sq_nonneg (t-1/2)]
  have hd : 0 < t^2*(1-t+t^2) := mul_pos (sq_pos_of_pos ht0) hq
  constructor
  · exact mul_pos (mul_pos ht0 (sub_pos.mpr ht1)) (by positivity)
  · nlinarith

theorem solution (x : Nat → Real) (hx : x 0 = 1/2)
    (hn : ∀ n, x (n+1) = x n*(1-x n)*(1+(x n)^2)) :
    ∀ n, 0 < x n ∧ x n < 1 := by
  intro n
  induction n with
  | zero => rw [hx]; norm_num
  | succ n ih =>
    obtain ⟨hpos, hlt⟩ := update_bounds (x n) ih.1 ih.2
    rw [hn]
    exact ⟨hpos, hlt.trans ih.2⟩

#print axioms solution
