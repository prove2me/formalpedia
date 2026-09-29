-- Prove2me | solution 1 for lean_workbook_plus_58944
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:08.248823+00:00
-- url     : https://prove2.me/submissions/9967bf9f-3557-4a0c-a0a9-bb1cc5ddcd7c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x * y ≤ 1) : 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) ≤ 2 / (1 + x * y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_nonneg hx hy])
