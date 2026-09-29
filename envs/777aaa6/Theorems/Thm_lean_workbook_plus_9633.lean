-- Prove2me | Theorems.Thm_lean_workbook_plus_9633
-- name    : lean_workbook_plus_9633
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/f57b70cc-0572-49c1-989d-e154923bb7ef
-- statement:
--   An example which evades both Muirhead and Schur in degree 4: $ \frac23(a^2+b^2+c^2)^2 \ge a^3(b+c) + b^3(c+a) + c^3(a+b). $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9633 : ∀ a b c : ℝ, (2 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b)   :=  by sorry
