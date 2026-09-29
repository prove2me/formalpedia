-- Prove2me | Theorems.Thm_lean_workbook_plus_82124
-- name    : lean_workbook_plus_82124
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/2736e416-aa8a-4fda-ad29-bf6510366700
-- statement:
--   $(x^2+y^2+z^2-xy-yz-zx)^2\geq 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82124 (x y z: ℝ) : (x^2 + y^2 + z^2 - x * y - x * z - y * z)^2 ≥ 0   :=  by sorry
