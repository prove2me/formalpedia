-- Prove2me | solution 1 for lean_workbook_plus_76557
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:11:44.011386+00:00
-- url     : https://prove2.me/submissions/7f60530a-963f-46e7-a3c5-c128d13a88f7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (a + b + c + d) ^ 3 ≥ 16 * (a * b * c + b * c * d + a * c * d + a * b * d) := by
  have h (x y z w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
      0 ≤ (x - y) ^ 2 * (x + y + 5 * (z + w)) := by positivity
  nlinarith [h a b c d ha hb hc hd, h a c b d ha hc hb hd,
    h a d b c ha hd hb hc, h b c a d hb hc ha hd,
    h b d a c hb hd ha hc, h c d a b hc hd ha hb]
