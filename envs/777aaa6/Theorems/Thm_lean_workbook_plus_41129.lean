-- Prove2me | Theorems.Thm_lean_workbook_plus_41129
-- name    : lean_workbook_plus_41129
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/cda7253c-0eb4-41c3-9abb-026e91608bb5
-- statement:
--   Prove that $4n + 1 < (\sqrt{n} + \sqrt{n+1})^2 < 4n + 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41129 : ∀ n : ℕ, 4 * n + 1 < (Real.sqrt n + Real.sqrt (n + 1))^2 ∧ (Real.sqrt n + Real.sqrt (n + 1))^2 < 4 * n + 3   :=  by sorry
