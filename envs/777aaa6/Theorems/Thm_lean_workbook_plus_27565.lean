-- Prove2me | Theorems.Thm_lean_workbook_plus_27565
-- name    : lean_workbook_plus_27565
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/c78713d9-e94a-4528-9da4-73e150764b7b
-- statement:
--   Given $g(n) = 3n^4 - 7n^3 - 9n^2 + 5n + 6$, prove that $g(n) > 0$ for $n > 8$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27565 (n : ℕ) (hn : n > 8) : 3 * n ^ 4 - 7 * n ^ 3 - 9 * n ^ 2 + 5 * n + 6 > 0   :=  by sorry
