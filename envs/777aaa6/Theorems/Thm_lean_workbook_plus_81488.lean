-- Prove2me | Theorems.Thm_lean_workbook_plus_81488
-- name    : lean_workbook_plus_81488
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/80b8e3ed-3ee4-4022-955a-bd6764206118
-- statement:
--   If $a, b, c$ are positive real numbers then \n $\frac{a}{{b + c}} + \frac{b}{{c + a}} + \frac{c}{{a + b}} \ge \frac{a}{{a + b}} + \frac{b}{{b + c}} + \frac{c}{{c + a}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81488 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (b + c) + b / (c + a) + c / (a + b) ≥ a / (a + b) + b / (b + c) + c / (c + a)   :=  by sorry
