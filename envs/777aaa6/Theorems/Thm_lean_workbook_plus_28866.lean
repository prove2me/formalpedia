-- Prove2me | Theorems.Thm_lean_workbook_plus_28866
-- name    : lean_workbook_plus_28866
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/19cdb98d-f3e0-4392-bdf7-4429d901bc17
-- statement:
--   Prove that for $ n>=0$ , $ 13| (4^{2n + 1} + 3^{n+2})$ using congruence.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28866 : ∀ n ≥ 0, (4^(2*n + 1) + 3^(n + 2)) % 13 = 0   :=  by sorry
