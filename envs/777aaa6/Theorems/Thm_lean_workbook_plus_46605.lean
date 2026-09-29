-- Prove2me | Theorems.Thm_lean_workbook_plus_46605
-- name    : lean_workbook_plus_46605
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/0b12b923-afa4-469d-834b-0d923e98ea64
-- statement:
--   and $\frac{(a+b+c)^{2}}{ab+bc+ca}\geq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46605 : ∀ a b c : ℝ, (a + b + c) ^ 2 / (a * b + b * c + a * c) ≥ 3   :=  by sorry
