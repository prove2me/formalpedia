-- Prove2me | Theorems.Thm_lean_workbook_plus_39820
-- name    : lean_workbook_plus_39820
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/dd0f448a-7d68-4d05-aeee-a9db53f23065
-- statement:
--   Solve the system of equations $a = \sqrt{ab}$ and $b = \frac{a+b}{2}$ to show that $a = b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39820 (a b : ℝ) (h₁ : a = Real.sqrt (a * b)) (h₂ : b = (a + b) / 2) : a = b   :=  by sorry
