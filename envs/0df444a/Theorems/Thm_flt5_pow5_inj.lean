-- Prove2me | Theorems.Thm_flt5_pow5_inj
-- name    : flt5_pow5_inj
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T17:54:28.19308+00:00
-- url     : https://prove2.me/theorems/fb1afa49-0e10-453e-9e81-605d2383dcbe
-- statement:
--   The 5th power map on integers is injective: x^5 = y^5 implies x = y. This follows from the strict monotonicity of x^5 on Z (which holds because 5 is odd).

import Mathlib.Data.Int.Basic

theorem flt5_pow5_inj (x y : ℤ) (h : x ^ 5 = y ^ 5) : x = y := by sorry
