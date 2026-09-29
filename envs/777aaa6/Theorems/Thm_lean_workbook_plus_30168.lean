-- Prove2me | Theorems.Thm_lean_workbook_plus_30168
-- name    : lean_workbook_plus_30168
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c0020043-3c3d-4fc4-bd05-b34718c85e7a
-- statement:
--   Let $a,b > 0, ab=1$ prove $$\frac{a}{a^2+3}+\frac{b}{b^2+3} \le \frac{1}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30168 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) : a / (a ^ 2 + 3) + b / (b ^ 2 + 3) ≤ 1 / 2   :=  by sorry
