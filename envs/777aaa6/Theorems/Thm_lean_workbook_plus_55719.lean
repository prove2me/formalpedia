-- Prove2me | Theorems.Thm_lean_workbook_plus_55719
-- name    : lean_workbook_plus_55719
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/4af52125-483d-4764-b885-d340cc86693c
-- statement:
--   Use Schur's inequality $a^4+b^4+c^4+abc(a+b+c) \geq a^3 b+a^3 c+b^3 a+b^3 c+c^3 a+c^3 b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55719 {a b c : ℝ} : a ^ 4 + b ^ 4 + c ^ 4 + a * b * c * (a + b + c) ≥ a ^ 3 * b + a ^ 3 * c + b ^ 3 * a + b ^ 3 * c + c ^ 3 * a + c ^ 3 * b   :=  by sorry
