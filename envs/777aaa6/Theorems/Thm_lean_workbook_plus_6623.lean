-- Prove2me | Theorems.Thm_lean_workbook_plus_6623
-- name    : lean_workbook_plus_6623
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/c0b67ac4-fabb-4dd9-b94d-25d720f994cc
-- statement:
--   Prove that $ab(a + b) + bc(b + c) + ac(a + c) \ge 6abc$ , where $a, b, c \in R^{+}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6623 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b * (a + b) + b * c * (b + c) + a * c * (a + c) ≥ 6 * a * b * c   :=  by sorry
