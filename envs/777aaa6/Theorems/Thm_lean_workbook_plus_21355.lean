-- Prove2me | Theorems.Thm_lean_workbook_plus_21355
-- name    : lean_workbook_plus_21355
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d2411bc1-5fcd-4c61-b3be-ccd2e2fb6e77
-- statement:
--   Let $ a, b, $ and $ c $ be positive real numbers. Suppose that $ a^2 +b^2 +c^2 +1.5abc = 4.5 $ . Show that $ a + b + c \le 3 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21355 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 1.5 * a * b * c = 4.5) : a + b + c ≤ 3   :=  by sorry
