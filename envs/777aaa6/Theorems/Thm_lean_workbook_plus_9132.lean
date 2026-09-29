-- Prove2me | Theorems.Thm_lean_workbook_plus_9132
-- name    : lean_workbook_plus_9132
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/55428f0f-19b6-470a-b6ea-8ee60ebf7410
-- statement:
--   Both $x$ and $y$ are positive real numbers, and the point $(x,y)$ lies on or above both of the lines having equations $2x+5y=10$ and $3x+4y=12$ . What is the least possible value of $8x+13y$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9132 (x y : ℝ) (h₁ : 2*x + 5*y ≥ 10) (h₂ : 3*x + 4*y ≥ 12) : 34 ≤ 8*x + 13*y   :=  by sorry
