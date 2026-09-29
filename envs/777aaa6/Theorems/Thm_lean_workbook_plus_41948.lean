-- Prove2me | Theorems.Thm_lean_workbook_plus_41948
-- name    : lean_workbook_plus_41948
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/9ecf3a3f-d3b7-40be-b9f0-2d9510467669
-- statement:
--   Prove that $(a+b+c)^6-27(a^2+b^2+c^2)(ab+bc+ca)^2=(a^2+b^2+c^2+8(ab+bc+ca))(a^2+b^2+c^2-ab-bc-ca)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41948 (a b c : ℝ) :
  (a + b + c) ^ 6 - 27 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) ^ 2 =
    (a ^ 2 + b ^ 2 + c ^ 2 + 8 * (a * b + b * c + c * a)) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) ^ 2   :=  by sorry
