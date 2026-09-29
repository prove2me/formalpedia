-- Prove2me | solution 1 for lean_workbook_plus_1312
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:23:42.78608+00:00
-- url     : https://prove2.me/submissions/12703f54-577a-4dde-9a69-0b7bfe29600d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y < 1) : (1 - x) / (1 + x) * (1 - y) / (1 + y) ≥ (1 - x - y) / (1 + x + y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
