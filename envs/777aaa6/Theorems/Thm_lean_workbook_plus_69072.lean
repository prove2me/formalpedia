-- Prove2me | Theorems.Thm_lean_workbook_plus_69072
-- name    : lean_workbook_plus_69072
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0306f7ac-0dbc-4b71-969e-9d4b62a9738b
-- statement:
--   Function $f: \mathbb{R} \mapsto \mathbb{R}$ is injective if and only if for all $x_1,x_2 \in \mathbb{R}$ we have $f(x_1) = f(x_2) \Rightarrow x_1 = x_2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69072 (f : ℝ → ℝ) : (∀ x y, f x = f y → x = y) ↔ Function.Injective f   :=  by sorry
