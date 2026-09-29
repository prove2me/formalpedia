-- Prove2me | solution 1 for lean_workbook_plus_8780
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:27.881153+00:00
-- url     : https://prove2.me/submissions/dc9dc39f-9d97-4886-8545-94b3283bba7b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z a b c : ℝ) (hx : x = a + b) (hy : y = b + c) (hz : z = c + a) (hab : a > 0 ∧ b > 0 ∧ c > 0) : a^3 + b^3 + c^3 + a^2 * b + b^2 * c + c^2 * a >= 2 * (a * b^2 + b * c^2 + c * a^2) := by
  rcases hab with ⟨ha,hb,hc⟩
  have h1 := mul_nonneg ha.le (sq_nonneg (a-c))
  have h2 := mul_nonneg hb.le (sq_nonneg (b-a))
  have h3 := mul_nonneg hc.le (sq_nonneg (c-b))
  nlinarith only [h1,h2,h3]
