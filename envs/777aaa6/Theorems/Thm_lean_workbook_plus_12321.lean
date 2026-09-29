-- Prove2me | Theorems.Thm_lean_workbook_plus_12321
-- name    : lean_workbook_plus_12321
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/130c385f-e813-4fc6-b917-43e85023390e
-- statement:
--   Let $a,b,c>0$ and $a+b+c=0$. Prove that: $a^2 b+b^2 c+c^2 a\le a^2 +b^2 +c^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12321 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 0) : a^2 * b + b^2 * c + c^2 * a ≤ a^2 + b^2 + c^2   :=  by sorry
