-- Prove2me | Theorems.Thm_lean_workbook_plus_15729
-- name    : lean_workbook_plus_15729
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b94a5e96-61a6-44a5-84b9-409d1e6b911a
-- statement:
--   Prove: $3(x^2 + y^2 + z^2)\geq (x + y + z)^2\geq 3(xy + yz + zx)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15729 (x y z : ℝ) : 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ (x + y + z) ^ 2 ∧ (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x)   :=  by sorry
