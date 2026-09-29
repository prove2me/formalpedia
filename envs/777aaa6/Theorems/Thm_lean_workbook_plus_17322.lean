-- Prove2me | Theorems.Thm_lean_workbook_plus_17322
-- name    : lean_workbook_plus_17322
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/727b4469-bbee-4628-9953-98282724efc4
-- statement:
--   Prove that $a^3b^3+b^3c^3+c^3a^3 \ge 3a^2b^2c^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17322 : ∀ a b c : ℝ, a^3 * b^3 + b^3 * c^3 + c^3 * a^3 ≥ 3 * a^2 * b^2 * c^2   :=  by sorry
