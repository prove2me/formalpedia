-- Prove2me | Theorems.Thm_lean_workbook_plus_51531
-- name    : lean_workbook_plus_51531
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/1fe05f8a-654b-48d4-9b83-cce9fd900411
-- statement:
--   $4(-\cos^2(x) + \cos(x) + \dfrac{1}{2}) = 4(-(\cos(x) - \dfrac{1}{2})^2 + \dfrac{3}{4})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51531 : 4 * (-(Real.cos x) ^ 2 + Real.cos x + 1 / 2) = 4 * (-((Real.cos x) - 1 / 2) ^ 2 + 3 / 4)   :=  by sorry
