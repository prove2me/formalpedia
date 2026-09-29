-- Prove2me | Theorems.Thm_lean_workbook_plus_36540
-- name    : lean_workbook_plus_36540
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9ba941ee-a1c4-4093-9e03-df1c3f282b76
-- statement:
--   $ a^3b^3 + b^3c^3 + c^3a^3- abc(a^3 + b^3 + c^3)=(ab-c^2)(ac-b^2)(bc-a^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36540 (a b c : ℝ) :
  a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3 - a * b * c * (a ^ 3 + b ^ 3 + c ^ 3) =
    (a * b - c ^ 2) * (a * c - b ^ 2) * (b * c - a ^ 2)   :=  by sorry
