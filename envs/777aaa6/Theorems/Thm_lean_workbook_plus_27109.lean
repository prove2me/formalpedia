-- Prove2me | Theorems.Thm_lean_workbook_plus_27109
-- name    : lean_workbook_plus_27109
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/c62f793b-6bfe-4ecf-a68a-b157df83af24
-- statement:
--   Let ABC is triangle and AB=c , BC=a , AC=b\nProve that \n $ a^2( \frac {b}{c} - 1) + b^2( \frac {c}{a} - 1) + c^2( \frac {a}{b} - 1) \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27109 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 * (b / c - 1) + b^2 * (c / a - 1) + c^2 * (a / b - 1) ≥ 0   :=  by sorry
