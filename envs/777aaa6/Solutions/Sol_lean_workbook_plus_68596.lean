-- Prove2me | solution 1 for lean_workbook_plus_68596
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:47:06.510677+00:00
-- url     : https://prove2.me/submissions/db70d30e-d883-4ae2-a27f-1925fe264c32

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem remainder_identity (x : ℝ) :
    47*x^9+90*x^8+x^7-52*x^6+137*x^5+318*x^4+247*x^3+88*x^2+14*x+1 =
      26*x^4*(x^2-1)^2+47*x^9+64*x^8+x^7+137*x^5+292*x^4+
        247*x^3+88*x^2+14*x+1 := by
  ring

theorem stronger_bound (x : ℝ) (hx : 0 ≤ x) :
    1+14*x ≤ 47*x^9+90*x^8+x^7-52*x^6+137*x^5+318*x^4+247*x^3+88*x^2+14*x+1 := by
  rw [remainder_identity]
  have h : 0 ≤ 26*x^4*(x^2-1)^2+47*x^9+64*x^8+x^7+137*x^5+292*x^4+
      247*x^3+88*x^2 := by positivity
  linarith only [h]

theorem solution : ∀ x : ℝ, x >= 0 →
    47*x^9+90*x^8+x^7-52*x^6+137*x^5+318*x^4+247*x^3+88*x^2+14*x+1 >= 0 := by
  intro x hx
  linarith only [stronger_bound x hx, hx]
