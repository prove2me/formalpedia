-- Prove2me | Theorems.Thm_lean_workbook_plus_18885
-- name    : lean_workbook_plus_18885
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d4c635ac-ba7e-41e1-b6e4-11b276fbef23
-- statement:
--   For $A$ , setting $x=0.5$ and $y=-0.75$ gives $y+x^2=-0.5$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18885  (x y : ℝ)
  (h₀ : x = 0.5)
  (h₁ : y = -0.75) :
  y + x^2 = -0.5   :=  by sorry
