-- Prove2me | Theorems.Thm_lean_workbook_plus_33971
-- name    : lean_workbook_plus_33971
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/de645619-af4d-4d40-8520-627b2ae4e714
-- statement:
--   $2+4+\cdots+2018=1009^2+1009$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33971 : ∑ k in Finset.range 1009, (2 * k + 2) = 1009^2 + 1009   :=  by sorry
