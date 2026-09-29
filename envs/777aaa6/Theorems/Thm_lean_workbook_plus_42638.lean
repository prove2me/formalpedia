-- Prove2me | Theorems.Thm_lean_workbook_plus_42638
-- name    : lean_workbook_plus_42638
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/63902764-e685-408a-9db1-a21fd1e29c77
-- statement:
--   after some tedious work we get\n$x^{13}+x+90 = (x^{11}+x^{10}-x^9-3x^8-x^7+5x^6+7x^5-3x^4-17x^3-11x^2+23x+45)(x^2-x+2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42638 : ∀ x : ℂ, x^13 + x + 90 = (x^11 + x^10 - x^9 - 3*x^8 - x^7 + 5*x^6 + 7*x^5 - 3*x^4 - 17*x^3 - 11*x^2 + 23*x + 45) * (x^2 - x + 2)   :=  by sorry
