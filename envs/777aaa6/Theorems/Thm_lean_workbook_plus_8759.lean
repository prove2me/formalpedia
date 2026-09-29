-- Prove2me | Theorems.Thm_lean_workbook_plus_8759
-- name    : lean_workbook_plus_8759
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/de781293-ea24-4568-b08d-b0ad32c83c87
-- statement:
--   $6\tan A=6\tan^3 A$ $\Longleftrightarrow$ $\tan A(\tan^2 A-1)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8759 : 6 * tan A = 6 * tan A ^ 3 ↔ tan A * (tan A ^ 2 - 1) = 0   :=  by sorry
