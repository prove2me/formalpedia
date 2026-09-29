-- Prove2me | Theorems.Thm_lean_workbook_plus_47547
-- name    : lean_workbook_plus_47547
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/2a36ab08-86c2-424b-a928-429b762efce2
-- statement:
--   Prove that $2(a^4+b^4+c^4+a^2bc+b^2ac+c^2ab)\geq 2(a^3b+a^3c+b^3a+b^3c+c^3a+c^3b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47547 (a b c : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4 + a ^ 2 * b * c + b ^ 2 * a * c + c ^ 2 * a * b) ≥ 2 * (a ^ 3 * b + a ^ 3 * c + b ^ 3 * a + b ^ 3 * c + c ^ 3 * a + c ^ 3 * b)   :=  by sorry
