-- Prove2me | Theorems.Thm_lean_workbook_plus_72234
-- name    : lean_workbook_plus_72234
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/deee415b-0ee1-4ec8-9576-1cabab5d9f4c
-- statement:
--   Why is $f(z)=\frac{1}{z^2-1}$ considered to have two isolated singularities - two simple poles at $z=1$ and $z=-1$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72234 : ∀ z : ℂ, (z^2 - 1)⁻¹ = 0 ↔ z = 1 ∨ z = -1   :=  by sorry
