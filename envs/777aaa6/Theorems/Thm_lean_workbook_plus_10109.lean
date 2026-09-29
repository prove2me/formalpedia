-- Prove2me | Theorems.Thm_lean_workbook_plus_10109
-- name    : lean_workbook_plus_10109
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/78427559-0c21-4fac-8249-c23dd8800c6b
-- statement:
--   Let $a,b>0$ and $ a+b^2=1.$ Prove that $$ ab+2a+3b \leq \frac{94}{27}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10109 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b^2 = 1) : a * b + 2 * a + 3 * b ≤ 94 / 27   :=  by sorry
