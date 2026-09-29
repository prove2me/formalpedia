-- Prove2me | Theorems.Thm_lean_workbook_plus_10203
-- name    : lean_workbook_plus_10203
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/94ba9c8f-ec8f-4fc5-8365-2adc7a7f0d44
-- statement:
--   Prove that ${r+1\choose 2} + {r+1\choose 3} = {r+2\choose 3}$ using Pascal's formula.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10203 (r : ℕ) : choose (r + 1) 2 + choose (r + 1) 3 = choose (r + 2) 3   :=  by sorry
