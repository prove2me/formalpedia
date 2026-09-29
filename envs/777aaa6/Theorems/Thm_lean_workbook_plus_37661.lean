-- Prove2me | Theorems.Thm_lean_workbook_plus_37661
-- name    : lean_workbook_plus_37661
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/0d486f63-5d9c-40f3-b2c0-d6c2fd097da6
-- statement:
--   Prove that \n\n $[5(a^2+b^2+c^2)-2(ab+bc+ca)]^2 \ge 15(a^4+b^4+c^4)+12abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37661 (a b c : ℝ) :
  (5 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a * b + b * c + c * a)) ^ 2 ≥
    15 * (a ^ 4 + b ^ 4 + c ^ 4) + 12 * a * b * c * (a + b + c)   :=  by sorry
