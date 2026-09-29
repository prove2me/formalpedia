-- Prove2me | Theorems.Thm_lean_workbook_plus_21878
-- name    : lean_workbook_plus_21878
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b70a23a1-42c1-4c8e-9008-3154095c14ba
-- statement:
--   Let $a, b\geq0 $ and $a^3+b^3= 2$ . Prove that $$ a^2+b^2\le a^5+b^5\le 2(a^2+b^2)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21878 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^3 + b^3 = 2) : a^2 + b^2 ≤ a^5 + b^5 ∧ a^5 + b^5 ≤ 2 * (a^2 + b^2)   :=  by sorry
