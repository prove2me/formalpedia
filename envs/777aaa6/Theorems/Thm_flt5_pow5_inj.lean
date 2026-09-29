-- Prove2me | Theorems.Thm_flt5_pow5_inj
-- name    : flt5_pow5_inj
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T17:54:28.19308+00:00
-- url     : https://prove2.me/theorems/eb2d4a7a-f2a9-40d2-910e-b6468b1b8672
-- statement:
--   The 5th power map on integers is injective: x^5 = y^5 implies x = y. This follows from the strict monotonicity of x^5 on Z (which holds because 5 is odd).

import Mathlib.Data.Int.Basic

theorem flt5_pow5_inj (x y : ℤ) (h : x ^ 5 = y ^ 5) : x = y := by sorry
