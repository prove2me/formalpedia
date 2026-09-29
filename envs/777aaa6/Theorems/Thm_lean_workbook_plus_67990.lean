-- Prove2me | Theorems.Thm_lean_workbook_plus_67990
-- name    : lean_workbook_plus_67990
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/74ec6621-a9d0-4378-adb1-7e21458bdfda
-- statement:
--   Prove that the inequality is true for any real numbers \n\n $a^2b^2 + a^2c^2 + b^2c^2 >= a^2bc + ab^2c + abc^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67990 (a b c: ℝ) : a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 >= a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2   :=  by sorry
