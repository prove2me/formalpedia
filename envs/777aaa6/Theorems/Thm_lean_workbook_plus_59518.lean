-- Prove2me | Theorems.Thm_lean_workbook_plus_59518
-- name    : lean_workbook_plus_59518
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/dc2981de-f353-4194-8b9b-cd27ba153da9
-- statement:
--   Let $ A = \cos(x) + i\sin(x)$ , $ B = \cos(y) + i\sin(y)$ , $ C = \cos(z) + i\sin(z)$ . Prove that $ A^n + B^n + C^n \in \mathbb{R}$ for all $ n \in \mathbb{N}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59518 (x y z : ℝ) (n : ℕ) : (cos x + sin x * I)^n + (cos y + sin y * I)^n + (cos z + sin z * I)^n ∈ Set.range (Complex.re)   :=  by sorry
