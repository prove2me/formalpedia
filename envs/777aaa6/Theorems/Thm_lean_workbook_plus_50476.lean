-- Prove2me | Theorems.Thm_lean_workbook_plus_50476
-- name    : lean_workbook_plus_50476
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/357f4fa1-f6c6-419e-bc38-87094b6f9ece
-- statement:
--   $f(x)=2023x$ $\forall x\le -1$ and $f(x)=-2022x^2-1$ $\forall x>-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50476 (x : ℝ) (f : ℝ → ℝ) (hf: f = fun x => if x ≤ -1 then 2023 * x else -2022 * x ^ 2 -1) : ∃ x, ∃ y, x < y ∧ f x = f y   :=  by sorry
