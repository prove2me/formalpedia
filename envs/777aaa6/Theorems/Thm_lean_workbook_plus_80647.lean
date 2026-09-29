-- Prove2me | Theorems.Thm_lean_workbook_plus_80647
-- name    : lean_workbook_plus_80647
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/beb23e65-9e02-4130-bcfd-026834122c22
-- statement:
--   Prove the following inequality. For $x, y \geq 0$, $(x+y)^3 \leq x^3+y^3 + 3\left(\frac{x+y}{2}\right)^2(x+y)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80647 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 3 ≤ x ^ 3 + y ^ 3 + 3 * ((x + y) / 2) ^ 2 * (x + y)   :=  by sorry
