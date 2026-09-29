-- Prove2me | Theorems.Thm_lean_workbook_plus_66419
-- name    : lean_workbook_plus_66419
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/08b767ce-5ead-4edd-9d99-c6bfbadaa9ff
-- statement:
--   Let $ a, b>0$ and $a+b \leq 1 . $ Prove that \n $$ \left(a+\frac{1}{b}\right)\left(b+\frac{1}{a}\right) \geq \frac{25}{4}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66419 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) : (a + 1 / b) * (b + 1 / a) ≥ 25 / 4   :=  by sorry
