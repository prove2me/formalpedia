-- Prove2me | Theorems.Thm_lean_workbook_plus_18941
-- name    : lean_workbook_plus_18941
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/462f7a1f-ce1b-4e29-bd76-6b780f6e48dc
-- statement:
--   Let $x = \ln a, y = \ln b, z = \ln c$ are positive reals with $z > y > x$ . We wish to show $\frac{z-y}{x}+\frac{x-z}{y}+\frac{y-x}{z}> 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18941 (x y z : ℝ) (h₁ : 0 < x ∧ 0 < y ∧ 0 < z) (h₂ : z > y) (h₃ : y > x) : (z - y) / x + (x - z) / y + (y - x) / z > 0   :=  by sorry
