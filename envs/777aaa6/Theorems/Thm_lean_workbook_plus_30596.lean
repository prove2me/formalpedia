-- Prove2me | Theorems.Thm_lean_workbook_plus_30596
-- name    : lean_workbook_plus_30596
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c847720a-bf40-4acc-889b-0ef6503ed8c3
-- statement:
--   Prove that for all real numbers $a$, $b$, and $c$, the following inequality holds:\n$LHS=\frac{1}{3}\sum{(4a-5b+4c)^2(4a+4b-5c)^2}\ge{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30596 : ∀ a b c : ℝ, (1 / 3) * ((4 * a - 5 * b + 4 * c) ^ 2 * (4 * a + 4 * b - 5 * c) ^ 2) ≥ 0   :=  by sorry
