-- Prove2me | Theorems.Thm_lean_workbook_plus_47186
-- name    : lean_workbook_plus_47186
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/db7765f1-7aa2-48ae-aa50-59de708fd6c6
-- statement:
--   Prove that if $a, b, c$ are the sides of a triangle, then $2(a^2 + b^2 + c^2) \geq (a + b + c)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47186 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 2 * (a^2 + b^2 + c^2) ≥ (a + b + c)^2  :=  by sorry
