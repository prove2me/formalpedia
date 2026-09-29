-- Prove2me | Theorems.Thm_lean_workbook_plus_41360
-- name    : lean_workbook_plus_41360
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/e8e0b15e-3698-4012-9dc0-df5e09bdcf97
-- statement:
--   If $a + b + c = 0$ , then $a^3b + b^3c + c^3a = -(a^2 + ab + b^2)^2$ is the negative of a square.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41360 {a b c : ℤ} (h : a + b + c = 0) :
    a^3 * b + b^3 * c + c^3 * a = -(a^2 + a * b + b^2)^2   :=  by sorry
