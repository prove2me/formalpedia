-- Prove2me | Theorems.Thm_lean_workbook_plus_62481
-- name    : lean_workbook_plus_62481
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/c3ac2f05-409f-45f6-961c-5e2dddbd9278
-- statement:
--   For any two real numbers $ a > b$ , we have that $ a > \dfrac{a + b}{2} > b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62481 (a b : ℝ) (h₁ : a > b) : a > (a + b) / 2 ∧ (a + b) / 2 > b   :=  by sorry
