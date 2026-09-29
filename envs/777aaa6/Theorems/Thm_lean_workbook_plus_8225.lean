-- Prove2me | Theorems.Thm_lean_workbook_plus_8225
-- name    : lean_workbook_plus_8225
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/52e06e0e-317e-4680-ad5c-086d529fc076
-- statement:
--   For non-negativee real numbers $a,b,c$ with $a^2+b^2+c^2+2abc=1$ prove that $a+b+c \leq \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8225 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) : a + b + c ≤ 3 / 2   :=  by sorry
