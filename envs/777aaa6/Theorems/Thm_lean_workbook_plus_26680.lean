-- Prove2me | Theorems.Thm_lean_workbook_plus_26680
-- name    : lean_workbook_plus_26680
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4673925c-5c19-4edc-9bb1-702d96ae4a75
-- statement:
--   Prove the following identity.\n$e^{4ix} = e^{2ix} * e^{2ix}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26680 : exp (4 * I * x) = exp (2 * I * x) * exp (2 * I * x)   :=  by sorry
