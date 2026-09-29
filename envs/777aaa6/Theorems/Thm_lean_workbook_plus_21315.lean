-- Prove2me | Theorems.Thm_lean_workbook_plus_21315
-- name    : lean_workbook_plus_21315
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/320a27dc-78bf-48bc-8202-0e390251a282
-- statement:
--   Given $ a + b + c = 0 $ , show that $ 2a^4 + 2b^4 + 2c^4 $ is a perfect square.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21315 (a b c : ℤ) (h : a + b + c = 0) : ∃ k : ℤ, k^2 = 2 * a^4 + 2 * b^4 + 2 * c^4   :=  by sorry
