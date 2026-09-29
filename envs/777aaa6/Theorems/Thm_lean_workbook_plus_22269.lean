-- Prove2me | Theorems.Thm_lean_workbook_plus_22269
-- name    : lean_workbook_plus_22269
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f9e7e71e-5e63-4a58-ae48-aa2eb57bd5af
-- statement:
--   Find the remainder when $f(x)$ is divided by $(x+1)(x-2)(x+3)$, given that $R_1(-3)=12$, $R_2(-1)=-6$, and $R_3(2)=8$, where $R_1(x)$, $R_2(x)$, and $R_3(x)$ are remainders when $f(x)$ is divided by $(x+1)(x-2)$, $(x-2)(x+3)$, and $(x+3)(x+1)$ respectively.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22269 (f : ℝ → ℝ) (R1 : ℝ → ℝ) (R2 : ℝ → ℝ) (R3 : ℝ → ℝ) (h1 : ∀ x, R1 x = f x % (x + 1) * (x - 2)) (h2 : ∀ x, R2 x = f x % (x - 2) * (x + 3)) (h3 : ∀ x, R3 x = f x % (x + 3) * (x + 1)) (h4 : R1 (-3) = 12) (h5 : R2 (-1) = -6) (h6 : R3 2 = 8) : ∀ x, f x % (x + 1) * (x - 2) * (x + 3) = -41 / 30 * x ^ 2 - 53 / 15 * x + 1 / 30   :=  by sorry
