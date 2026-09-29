-- Prove2me | Theorems.Thm_lean_workbook_plus_490
-- name    : lean_workbook_plus_490
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/38869cd8-3297-47fb-a6a6-69712c62a86c
-- statement:
--   Use another application of AM-GM to prove that $27(a^2+b^2+c^2)(ab+bc+ca)^2\geq 81abc(a+b+c)(a^2+b^2+c^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_490 (a b c : ℝ) : 27 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) ^ 2 ≥ 81 * a * b * c * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
