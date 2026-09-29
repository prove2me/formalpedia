-- Prove2me | Theorems.Thm_lean_workbook_plus_48471
-- name    : lean_workbook_plus_48471
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/95204277-9d12-4ff8-8c68-6173239dbf0d
-- statement:
--   Let be $ x\in [-1,1]$ , and $ a,b,c\in \mathbb{R}$ such that $ |ax^2+bx+c|\le 1\ ,\ (\forall)x\in [-1,1]$ . Without second degree function prove that $ |a|+|b|+|c|\le 4$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48471 (a b c : ℝ) (h : ∀ x ∈ Set.Icc (-1) 1, abs (a * x ^ 2 + b * x + c) ≤ 1) :
  abs a + abs b + abs c ≤ 4   :=  by sorry
