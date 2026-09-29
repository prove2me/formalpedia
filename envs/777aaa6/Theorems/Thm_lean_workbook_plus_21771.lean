-- Prove2me | Theorems.Thm_lean_workbook_plus_21771
-- name    : lean_workbook_plus_21771
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/c695551c-1c0f-4673-87f9-4e2f5d82e841
-- statement:
--   Derivation of the identity: \\( \\left(\\frac{n}{\\sqrt{n(n+1)}}\\right)^2+\\left(\\frac{1}{\\sqrt{n+1}}\\right)^2=1 \\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21771 (n : ℕ) (hn : n ≠ 0) : ((n:ℝ) / √(n * (n + 1)))^2 + (1 / √(n + 1))^2 = 1   :=  by sorry
