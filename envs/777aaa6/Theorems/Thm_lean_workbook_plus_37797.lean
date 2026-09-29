-- Prove2me | Theorems.Thm_lean_workbook_plus_37797
-- name    : lean_workbook_plus_37797
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/3ff9d7d7-60d2-44f4-8d3f-d5788941df63
-- statement:
--   By AM-GM, prove that $\frac{3}{2abc} \geq \frac{81}{2(a+b+c)^3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37797 : ∀ a b c : ℝ, (3 / (2 * a * b * c) ≥ 81 / (2 * (a + b + c) ^ 3))   :=  by sorry
