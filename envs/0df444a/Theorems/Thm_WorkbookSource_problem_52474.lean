-- Prove2me | Theorems.Thm_WorkbookSource_problem_52474
-- name    : WorkbookSource.problem_52474
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:11.216707+00:00
-- url     : https://prove2.me/theorems/d8df80f3-1f0d-4906-acc0-d7c5c6bca80c
-- title:
--   A bound for the largest three of seven ordered numbers
-- statement:
--   Let $x_1 \leq x_2 \leq ... \leq x_7$. Then $x_5+x_6+x_7 \geq \frac{3}{7}(x_1+...+x_7)=142\frac{2}{7}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52474` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52474; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_52474 (x : ℕ → ℝ) (hx: x 1 ≤ x 2 ∧ x 2 ≤ x 3 ∧ x 3 ≤ x 4 ∧ x 4 ≤ x 5 ∧ x 5 ≤ x 6 ∧ x 6 ≤ x 7): x 5 + x 6 + x 7 ≥ 3/7 * (x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7)  :=  by sorry
