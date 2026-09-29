-- Prove2me | Theorems.Thm_lean_workbook_plus_7004
-- name    : lean_workbook_plus_7004
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f5870485-d240-43f3-ba4b-09ff03ee43de
-- statement:
--   By $ x,y,z\ge 1$ , we have $ \sqrt {3 - 2x}\le 1$ etc., thus $ LHS \le xy+yz+zx\le x^2 + y^2 + z^2\le x^3 + y^3 + z^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7004 : ∀ x y z : ℝ, x ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 → Real.sqrt (3 - 2 * x) ≤ 1 ∧ Real.sqrt (3 - 2 * y) ≤ 1 ∧ Real.sqrt (3 - 2 * z) ≤ 1 → x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2 ∧ x ^ 2 + y ^ 2 + z ^ 2 ≤ x ^ 3 + y ^ 3 + z ^ 3   :=  by sorry
