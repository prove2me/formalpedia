-- Prove2me | Theorems.Thm_lean_workbook_plus_13332
-- name    : lean_workbook_plus_13332
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b4e0d2e3-e462-419e-9919-460d7df6c648
-- statement:
--   Thus it suffices to show that \n\n $$(b+c)^4-b^4-c^4-14b^2c^2=f(0, b, c)\ge 0$$ which becomes clear after expanding: \n\n $$4bc(b-c)^2\ge 0.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13332 : ∀ b c : ℝ, (b + c) ^ 4 - b ^ 4 - c ^ 4 - 14 * b ^ 2 * c ^ 2 ≥ 0   :=  by sorry
