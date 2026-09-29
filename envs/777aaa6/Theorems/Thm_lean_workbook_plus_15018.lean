-- Prove2me | Theorems.Thm_lean_workbook_plus_15018
-- name    : lean_workbook_plus_15018
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/3098219f-7caf-4ae3-8492-bbf5ffb40320
-- statement:
--   Hence \n $\frac1{\sqrt{a}+\sqrt{(a+b)(a+c)}} \le \frac19\left(\frac1{\sqrt{a}}+\frac4{\sqrt{(a+b)(a+c)}}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15018 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (√a + √((a + b) * (a + c))) ≤ 1 / 9 * (1 / √a + 4 / √((a + b) * (a + c)))   :=  by sorry
