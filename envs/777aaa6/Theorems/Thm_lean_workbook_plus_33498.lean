-- Prove2me | Theorems.Thm_lean_workbook_plus_33498
-- name    : lean_workbook_plus_33498
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/5edb44df-08fe-4117-af73-2864347ff80c
-- statement:
--   $ A-B = 2m^2 - mn - n^2 = (m-n)(2m+n) \qquad(1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33498 (m n : ℤ) : A - B = 2 * m ^ 2 - m * n - n ^ 2 ↔ A - B = (m - n) * (2 * m + n)   :=  by sorry
