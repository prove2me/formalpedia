-- Prove2me | Theorems.Thm_lean_workbook_plus_30084
-- name    : lean_workbook_plus_30084
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0fc4d5eb-9391-488b-8f26-dbd4865cca9c
-- statement:
--   Find all functions $f: \mathbb{R}\to\mathbb{R}$ such that $yf(x)=xf(y)$ for all real $x,y$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30084 (f : ℝ → ℝ): (∀ x y :ℝ, y * f x = x * f y) ↔ ∃ k:ℝ, ∀ x:ℝ, f x = k * x   :=  by sorry
