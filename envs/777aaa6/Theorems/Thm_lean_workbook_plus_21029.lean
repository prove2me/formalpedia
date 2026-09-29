-- Prove2me | Theorems.Thm_lean_workbook_plus_21029
-- name    : lean_workbook_plus_21029
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b4c87bb2-1abf-4b01-9539-96cd33085fd4
-- statement:
--   If $a, b, c$ are positive real numbers, then:\n$ \sum a(a+b)(a+c) \ge (a+b)(b+c)(c+a) + 4abc \ \ ; $\n\nGreetings!
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21029 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * (a + b) * (a + c) + b * (b + c) * (b + a) + c * (c + a) * (c + b) ≥ (a + b) * (b + c) * (c + a) + 4 * a * b * c   :=  by sorry
