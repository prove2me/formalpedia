-- Prove2me | Theorems.Thm_lean_workbook_plus_48092
-- name    : lean_workbook_plus_48092
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/0ada56e6-a14c-4dc0-8174-d8c4ad8b8762
-- statement:
--   $ (a-b)^4+(b-c)^4+(c-a)^4+(a^4+b^4+c^4-a^2bc+b^2ca+c^2ab)\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48092 {a b c : ℝ} : (a - b) ^ 4 + (b - c) ^ 4 + (c - a) ^ 4 + (a ^ 4 + b ^ 4 + c ^ 4 - a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ≥ 0   :=  by sorry
