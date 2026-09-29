-- Prove2me | Theorems.Thm_lean_workbook_plus_18409
-- name    : lean_workbook_plus_18409
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a5bdd4d4-c1e3-48b1-b939-a618fe5559dc
-- statement:
--   Prove that for all real numbers a,b,c \n\n $a^2b^2+a^2c^2+b^2c^2\geq a^2bc+ab^2c+abc^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18409 (a b c : ℝ) : a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 ≥ a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2   :=  by sorry
