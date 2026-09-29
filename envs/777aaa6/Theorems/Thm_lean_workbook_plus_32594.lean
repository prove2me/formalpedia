-- Prove2me | Theorems.Thm_lean_workbook_plus_32594
-- name    : lean_workbook_plus_32594
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/77b63d94-cdfc-4a17-be06-f1fb14be9415
-- statement:
--   Let $a,b$ are real numbers and satisfy $0<b<a \leq 4$ and $2 a b \leq 3 a+4 b$ . Prove that $$a^{2}+b^{2}\leq 25$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32594 (a b : ℝ) (h₁ : 0 < b ∧ b < a ∧ a ≤ 4) (h₂ : 2 * a * b ≤ 3 * a + 4 * b) : a^2 + b^2 ≤ 25   :=  by sorry
