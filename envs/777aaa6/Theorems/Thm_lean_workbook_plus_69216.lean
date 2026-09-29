-- Prove2me | Theorems.Thm_lean_workbook_plus_69216
-- name    : lean_workbook_plus_69216
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/14aaaa15-bbab-4873-a00a-c650a4ded64b
-- statement:
--   Let $a,b $ are non-negative real numbers such that $a^2+b^2=6 .$ Prove that \n\n $$\alpha a+\beta b\le\sqrt{6\left({\alpha}^2+{\beta}^2\right)}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69216 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2 + b^2 = 6) (α β : ℝ) : α * a + β * b ≤ Real.sqrt (6 * (α^2 + β^2))   :=  by sorry
