-- Prove2me | Theorems.Thm_lean_workbook_plus_2378
-- name    : lean_workbook_plus_2378
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/4388267b-be7b-4481-bd23-8f263e8ccc65
-- statement:
--   All squares are either $1(\mod {4})$ or $0 (\mod {4})$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2378 : ∀ n : ℤ, n ^ 2 ≡ 0 [ZMOD 4] ∨ n ^ 2 ≡ 1 [ZMOD 4]   :=  by sorry
