-- Prove2me | Theorems.Thm_lean_workbook_plus_64892
-- name    : lean_workbook_plus_64892
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/efcd0f82-aa2a-4310-933b-c696a2cc1cc2
-- statement:
--   Prove that $14(a^2+b^2+c^2-ab-bc-ca)^2+9(a^2+b^2+c^2)(ab+bc+ca)\ge 27abc(a+b+c)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64892 (a b c : ℝ) :
  14 * (a^2 + b^2 + c^2 - a * b - b * c - c * a)^2 + 9 * (a^2 + b^2 + c^2) * (a * b + b * c + c * a) ≥ 27 * a * b * c * (a + b + c)   :=  by sorry
