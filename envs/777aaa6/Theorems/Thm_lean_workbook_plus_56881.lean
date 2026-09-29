-- Prove2me | Theorems.Thm_lean_workbook_plus_56881
-- name    : lean_workbook_plus_56881
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/35676666-cba8-41fb-bd62-d117a626f5bd
-- statement:
--   prove $\frac{a(3-a^2)}{2-a^2} \geq 2a^2$ which is equivalent to $(a-1)^2(2a+3) \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56881 : ∀ a : ℝ, (a * (3 - a ^ 2) / (2 - a ^ 2) ≥ 2 * a ^ 2)   :=  by sorry
