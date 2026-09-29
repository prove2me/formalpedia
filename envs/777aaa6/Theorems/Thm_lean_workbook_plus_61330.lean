-- Prove2me | Theorems.Thm_lean_workbook_plus_61330
-- name    : lean_workbook_plus_61330
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/6149d747-3fb3-4cd8-a1bf-4cce46780f5e
-- statement:
--   Prove that for all real numbers $x,y,z$ the following inequality holds: $x^2+y^2+z^2-xy-yz-xz \ge \frac{3}{4}(x-y)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61330 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - x * z ≥ 3 / 4 * (x - y) ^ 2   :=  by sorry
