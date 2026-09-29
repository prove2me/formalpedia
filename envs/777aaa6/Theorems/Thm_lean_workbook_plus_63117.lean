-- Prove2me | Theorems.Thm_lean_workbook_plus_63117
-- name    : lean_workbook_plus_63117
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/dda40340-0cbe-41fa-ac55-39fdc8a077d1
-- statement:
--   prove that: $\frac{3^2}{2^2}(1-xyz) \geq (1-x)(yz-1)+(1-y)(xz-1)+(1-z)(xy-1)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63117 : ∀ x y z : ℝ, (3^2 / 2^2) * (1 - x * y * z) ≥ (1 - x) * (y * z - 1) + (1 - y) * (x * z - 1) + (1 - z) * (x * y - 1) ∧ (1 - x) * (y * z - 1) + (1 - y) * (x * z - 1) + (1 - z) * (x * y - 1) ≥ 0   :=  by sorry
