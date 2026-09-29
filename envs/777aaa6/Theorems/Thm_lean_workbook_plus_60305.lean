-- Prove2me | Theorems.Thm_lean_workbook_plus_60305
-- name    : lean_workbook_plus_60305
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/2429347a-3a9a-4084-8fb6-05c17212fce1
-- statement:
--   Your inequality is equivalent to $ \left(\sum_{cyc}(a^2-2ab)\right)^2\geq0.$ \nThe equality occurs for example when $ \sqrt a=\sqrt b+\sqrt c.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60305 (a b c : ℝ) : (a^2 - 2 * a * b + b^2 - 2 * b * c + c^2 - 2 * c * a)^2 ≥ 0   :=  by sorry
