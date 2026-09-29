-- Prove2me | Theorems.Thm_lean_workbook_plus_40320
-- name    : lean_workbook_plus_40320
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/deae3065-cfb0-4a7b-975b-cdac4659025f
-- statement:
--   Let $a, b\geq 1$ and $ a+\frac{1}{a^2} \geq b-\frac{2}{b^2}.$ Show that $$a\geq \frac{b}{2}-\frac{1}{b^2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40320 (a b : ℝ) (hab : 1 ≤ a ∧ 1 ≤ b) (h : a + 1 / a ^ 2 ≥ b - 2 / b ^ 2) : a ≥ b / 2 - 1 / b ^ 2   :=  by sorry
