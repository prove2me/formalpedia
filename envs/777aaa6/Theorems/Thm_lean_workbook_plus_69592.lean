-- Prove2me | Theorems.Thm_lean_workbook_plus_69592
-- name    : lean_workbook_plus_69592
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/44451e58-5434-43e7-89b3-a00d014306ec
-- statement:
--   Let a>=c>=0 and b>=d>=0 . Prove that \((a+b+c+d)^2\ge 8(ad+bc)\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69592 (a b c d : ℝ) (h1 : a ≥ c ∧ c ≥ 0) (h2 : b ≥ d ∧ d ≥ 0) :
  (a + b + c + d) ^ 2 ≥ 8 * (a * d + b * c)   :=  by sorry
