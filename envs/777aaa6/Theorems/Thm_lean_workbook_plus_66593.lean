-- Prove2me | Theorems.Thm_lean_workbook_plus_66593
-- name    : lean_workbook_plus_66593
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/4162219b-c138-4662-ac77-ef147b6d4683
-- statement:
--   It remains to prove that $32a^{5}+32a^{4}-16a^{3}-16a^{2}+9a-1 \ge 0 $ for all $1 \ge a \ge \frac{1}{5}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66593 (a : ℝ) (ha1 : 1 ≥ a ∧ a ≥ 1/5) : 32*a^5 + 32*a^4 - 16*a^3 - 16*a^2 + 9*a - 1 ≥ 0   :=  by sorry
