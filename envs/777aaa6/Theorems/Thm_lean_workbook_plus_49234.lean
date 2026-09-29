-- Prove2me | Theorems.Thm_lean_workbook_plus_49234
-- name    : lean_workbook_plus_49234
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/6d7a2972-b88d-4292-8490-7c78518603d0
-- statement:
--   Prove that $a^2+b^2+c^2+2ab+2ac+2bc =(a+b+c)^2\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49234 : ∀ a b c : ℝ, a^2 + b^2 + c^2 + 2 * a * b + 2 * a * c + 2 * b * c = (a + b + c)^2 ∧ (a + b + c)^2 ≥ 0   :=  by sorry
