-- Prove2me | Theorems.Thm_lean_workbook_plus_768
-- name    : lean_workbook_plus_768
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/5526bdd0-e1c6-4260-8de4-85dc4936e7af
-- statement:
--   Find all function f:R->R ,s.t. $f(xy)=xf(y)$ for any $x,y\in{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_768 (f : ℝ → ℝ):(∀ x y, f (x * y) = x * f y) ↔ ∃ l:ℝ, ∀ x, f x = x * l   :=  by sorry
