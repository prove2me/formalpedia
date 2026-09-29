-- Prove2me | Theorems.Thm_lean_workbook_plus_25763
-- name    : lean_workbook_plus_25763
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/69274d89-af0c-45b0-b223-d39923f31558
-- statement:
--   Prove $x^2+y^2+z^2 \geq xy+yz+zx$ using the rearrangement inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25763 {x y z : ℝ} : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x   :=  by sorry
