-- Prove2me | Theorems.Thm_lean_workbook_plus_28539
-- name    : lean_workbook_plus_28539
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/47a5950d-c109-4bf0-a150-6e0c5d6976a6
-- statement:
--   $4\sin(x)(\cos(x) - \dfrac{\cos(2x)}{2}) = 4\sin(x)(-\cos^2(x) + \cos(x) + \dfrac{1}{2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28539 : 4 * sin x * (cos x - cos (2 * x) / 2) = 4 * sin x * (- cos x ^ 2 + cos x + 1 / 2)   :=  by sorry
