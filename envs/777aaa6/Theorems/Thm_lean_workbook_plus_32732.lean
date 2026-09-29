-- Prove2me | Theorems.Thm_lean_workbook_plus_32732
-- name    : lean_workbook_plus_32732
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/65f6739d-b4f1-4735-bb72-a3c07e31025e
-- statement:
--   If $x,y\in(1,3)$ show that $|(x-2)(y-2)|<1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32732 (x y : ℝ) (hx : 1 < x ∧ x < 3) (hy : 1 < y ∧ y < 3) : |(x - 2) * (y - 2)| < 1   :=  by sorry
