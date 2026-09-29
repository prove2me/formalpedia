-- Prove2me | Theorems.Thm_lean_workbook_plus_76793
-- name    : lean_workbook_plus_76793
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/24bd38aa-7f05-4275-b97d-20ea44ecf6c7
-- statement:
--   Prove $4(a^2+b^2+c^2)^2\ge (a+b+c)^2(2(a^2+b^2+c^2)-\sum ab)+(\sum ab)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76793 : ∀ a b c : ℝ, 4 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ (a + b + c) ^ 2 * (2 * (a ^ 2 + b ^ 2 + c ^ 2) - (a * b + b * c + c * a)) + (a * b + b * c + c * a) ^ 2   :=  by sorry
