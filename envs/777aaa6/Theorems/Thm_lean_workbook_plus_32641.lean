-- Prove2me | Theorems.Thm_lean_workbook_plus_32641
-- name    : lean_workbook_plus_32641
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/be89c785-8695-4335-8dfa-e2f27f597c34
-- statement:
--   Find $ z_1,\ z_2,\ z_3\in\mathbb{C}$ such that $ |z_1|=|z_2|=|z_3|=a,\ z_1z_2z_3=a^3,\ a\in\mathbb{R},\ a>0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32641 (a : ℝ) (ha : 0 < a) : ∃ z1 z2 z3 : ℂ, ‖z1‖ = a ∧ ‖z2‖ = a ∧ ‖z3‖ = a ∧ z1 * z2 * z3 = a ^ 3   :=  by sorry
