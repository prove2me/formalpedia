-- Prove2me | Theorems.Thm_lean_workbook_plus_60732
-- name    : lean_workbook_plus_60732
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/a42b3c44-deab-4873-a190-3b7e032a2616
-- statement:
--   Determine if $1^4 + 2^4 + 3^4 + 4^4 + 5^4$ is congruent to $3$ modulo $6$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60732 :
  (1^4 + 2^4 + 3^4 + 4^4 + 5^4) % 6 = 3   :=  by sorry
