-- Prove2me | Theorems.Thm_lean_workbook_plus_24734
-- name    : lean_workbook_plus_24734
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/fba74e57-b916-4103-9409-572fd11b92a8
-- statement:
--   Evaluate $\sum_{i=1}^4\sum_{j=1}^4(i-j)^2$ . (Source: Intermediate Algebra)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24734 (A : Matrix (Fin 4) (Fin 4) ℤ) : ∑ i : Fin 4, ∑ j : Fin 4, (i - j) ^ 2 = 40   :=  by sorry
