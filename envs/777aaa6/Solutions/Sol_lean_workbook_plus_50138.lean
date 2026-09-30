-- Prove2me | solution 1 for lean_workbook_plus_50138
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:12:39.77223+00:00
-- url     : https://prove2.me/submissions/892ec46d-c857-4c5d-80e8-8bdd31b5a20a

import Mathlib
set_option autoImplicit false

theorem solution (x y z a b c : ℝ) (hab : 0 < a ∧ 0 < b ∧ 0 < c) (h : x = (b - c) / (b + c) ∧ y = (c - a) / (c + a) ∧ z = (a - b) / (a + b)) : -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ -1 ≤ z ∧ z ≤ 1 ∧ x + y + z + x * y * z = 0   := by
  have bound (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      -1 < (u - v) / (u + v) ∧ (u - v) / (u + v) < 1 := by
    have hd : 0 < u + v := add_pos hu hv
    constructor
    · apply (lt_div_iff₀ hd).2
      linarith only [hu]
    · apply (div_lt_iff₀ hd).2
      linarith only [hv]
  rcases hab with ⟨ha, hb, hc⟩
  rcases h with ⟨rfl, rfl, rfl⟩
  refine ⟨(bound b c hb hc).1.le, (bound b c hb hc).2.le,
    (bound c a hc ha).1.le, (bound c a hc ha).2.le,
    (bound a b ha hb).1.le, (bound a b ha hb).2.le, ?_⟩
  field_simp [ne_of_gt (add_pos hb hc), ne_of_gt (add_pos hc ha),
    ne_of_gt (add_pos ha hb)] <;> ring

#print axioms solution
