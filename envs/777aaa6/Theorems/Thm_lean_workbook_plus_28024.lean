-- Prove2me | Theorems.Thm_lean_workbook_plus_28024
-- name    : lean_workbook_plus_28024
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/bf5443b3-a2e9-4741-be8c-8253e80decf9
-- statement:
--   Let $ x,\ y,\ z$ be real numbers such that $ |x| \leq 1,\ |y| \leq 1,\ |z| \leq 1$ . Prove that $ xyz \geq x + y + z - 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28024 (x y z : ℝ) (hx : abs x ≤ 1) (hy : abs y ≤ 1) (hz : abs z ≤ 1) : x*y*z ≥ x + y + z - 2   :=  by sorry
