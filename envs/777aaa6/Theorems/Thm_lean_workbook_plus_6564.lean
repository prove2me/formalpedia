-- Prove2me | Theorems.Thm_lean_workbook_plus_6564
-- name    : lean_workbook_plus_6564
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/faa9fbe0-4e9f-4430-a506-2da7e8f60768
-- statement:
--   6 boys total choose 3 boys, 5 girls total choose 2 girls, ans is $\binom{6}{3}\binom{5}{2}=(20)(10)=\boxed{200}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6564 :
  Nat.choose 6 3 * Nat.choose 5 2 = 200   :=  by sorry
