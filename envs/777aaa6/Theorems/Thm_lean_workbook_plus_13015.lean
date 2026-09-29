-- Prove2me | Theorems.Thm_lean_workbook_plus_13015
-- name    : lean_workbook_plus_13015
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/7077efeb-eb58-4320-939a-f79cecf7ded6
-- statement:
--   Prove that $x^2 + y^2 + z^2 \geq xy + xz + yz$ for all real numbers $x, y, z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13015 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z   :=  by sorry
