-- Prove2me | Theorems.Thm_lean_workbook_plus_54528
-- name    : lean_workbook_plus_54528
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/60b15a3a-699d-4620-a2c6-2822b0693c12
-- statement:
--   Is this inequality correct? \n $\sum a^4+3\sum a^2b^2\geq 2\sum a^3b+2\sum ab^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54528 : ∀ a b c : ℝ, a * b * c = 1 → a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2) ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 2 * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3)   :=  by sorry
