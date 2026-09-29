-- Prove2me | Theorems.Thm_lean_workbook_plus_2717
-- name    : lean_workbook_plus_2717
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ef5cf2ea-ba38-45d4-b967-158c5cf60b75
-- statement:
--   Prove $(a+b+c)^2 \geq 3(ab+bc+ca)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2717 {a b c : ℝ} : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + a * c)   :=  by sorry
