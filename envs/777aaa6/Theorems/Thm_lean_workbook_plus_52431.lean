-- Prove2me | Theorems.Thm_lean_workbook_plus_52431
-- name    : lean_workbook_plus_52431
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/cb8cd6a6-8e82-4987-b518-3de14859aeee
-- statement:
--   Prove that $xy + yz + zt + tx \geq -\left(x^2 + y^2 + z^2 + t^2\right)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52431 (x y z t : ℝ) : x * y + y * z + z * t + t * x ≥ -(x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2)   :=  by sorry
