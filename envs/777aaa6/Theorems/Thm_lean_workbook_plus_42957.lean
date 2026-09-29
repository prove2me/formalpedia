-- Prove2me | Theorems.Thm_lean_workbook_plus_42957
-- name    : lean_workbook_plus_42957
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c34da0cb-3709-4e9b-a022-1efc4eb2ead9
-- statement:
--   How would you evaluate ${6\choose{0}}{-6\choose{11}}+{6\choose{1}}{-6\choose{7}}+{6\choose{2}}{-6\choose{3}}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42957 (h₁ : 0 < 6) (h₂ : 0 < 11) (h₃ : 0 < 7) (h₄ : 0 < 3) : (choose 6 0 - choose 6 11) + (choose 6 1 - choose 6 7) + (choose 6 2 - choose 6 3) = 126   :=  by sorry
