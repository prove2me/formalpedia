-- Prove2me | Theorems.Thm_lean_workbook_plus_18413
-- name    : lean_workbook_plus_18413
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/bf6dd52d-3b03-492f-a595-894c9d2a6f7b
-- statement:
--   Write the function $f(x) = \begin{cases} x^2 & x\ge 0 \ 1 & x< 0 \end{cases} $ in Mathematica
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18413 (f : ℝ → ℝ) (x : ℝ) (hf: f x = if x >= 0 then x^2 else 1) : f x = if x >= 0 then x^2 else 1   :=  by sorry
