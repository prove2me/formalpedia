-- Prove2me | Theorems.Thm_lean_workbook_plus_8419
-- name    : lean_workbook_plus_8419
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/90f9068f-00e7-4e48-873f-499f86d5546c
-- statement:
--   If $n$ is congruent to $4$ modulo $8$, then it can't be congruent to $3$ modulo $4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8419 : n ≡ 4 [ZMOD 8] → ¬ n ≡ 3 [ZMOD 4]   :=  by sorry
