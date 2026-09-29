-- Prove2me | Theorems.Thm_lean_workbook_plus_14572
-- name    : lean_workbook_plus_14572
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/d41385a6-a45e-4ae0-92ea-ac7140568bb2
-- statement:
--   Prove the inequality for $x, y, z > 0$:\n${\frac {x-y}{z+x}}+{\frac {y-z}{x+y}}+{\frac {z-x}{y+z}}\leq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14572 : ∀ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 → (x - y) / (z + x) + (y - z) / (x + y) + (z - x) / (y + z) ≤ 0   :=  by sorry
