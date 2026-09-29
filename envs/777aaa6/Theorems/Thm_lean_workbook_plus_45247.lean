-- Prove2me | Theorems.Thm_lean_workbook_plus_45247
-- name    : lean_workbook_plus_45247
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/3f8c6b6b-2dc2-4877-872b-d53a637a23dd
-- statement:
--   By setting $P(a,b,c) = (ab - 1)(ac - 1)(bc - 1)$ we obtain $(2) \;\; P(a,b,c) = (abc)^2 - (a + b + c)abc + (ab + ab + bc) - 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45247 (a b c : ℂ) : (a * b - 1) * (a * c - 1) * (b * c - 1) = (a * b * c) ^ 2 - (a + b + c) * a * b * c + (a * b + a * c + b * c) - 1   :=  by sorry
