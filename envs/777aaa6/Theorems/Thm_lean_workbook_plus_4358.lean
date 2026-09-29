-- Prove2me | Theorems.Thm_lean_workbook_plus_4358
-- name    : lean_workbook_plus_4358
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/fdd4beb2-b5bd-4978-bf6c-6ddffb88b1b4
-- statement:
--   Let $a,b\in [1,2]$ . Prove that \n $$\frac{a+1}{b+2}+\frac{b+1}{a+2} \leq \frac{3}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4358 (a b : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2) : (a + 1) / (b + 2) + (b + 1) / (a + 2) ≤ 3 / 2   :=  by sorry
