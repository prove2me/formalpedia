-- Prove2me | Theorems.Thm_lean_workbook_plus_41799
-- name    : lean_workbook_plus_41799
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/4a7c3cb4-b232-41db-8415-54de2c0694eb
-- statement:
--   Prove the following identity.\n$sin(4x) = 8sin(x)cos^3(x)-4sin(x)cos(x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41799 : sin (4*x) = 8 * sin x * cos x ^ 3 - 4 * sin x * cos x   :=  by sorry
