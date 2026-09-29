-- Prove2me | solution 1 for lean_workbook_plus_38660
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:33.074645+00:00
-- url     : https://prove2.me/submissions/10bae7b4-4a5d-41f4-a5d8-c042f2baadac

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : a + b + c = 0) :
  a^3 + b^3 + c^3 = 3 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
