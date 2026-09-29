-- Prove2me | Theorems.Thm_lean_workbook_plus_82031
-- name    : lean_workbook_plus_82031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/6904ca9d-d656-47ea-9cd5-bd4a49bb5a82
-- statement:
--   Let $ a,b,c\ge 0$ such that $ a + b + c = 3$ . Find the maximum value of: $ V = a^3b + b^3c + c^3a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82031 (a b c V: ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3) (hV: V = a^3 * b + b^3 * c + c^3 * a): (a = 4/3 ∧ b = 4/3 ∧ c = 4/3 → V = 27 * (4/27)^4) ∧ (a = 4/3 ∧ b = 4/3 ∧ c = 4/3 → ∀ x y z : ℝ, x + y + z = 3 ∧ x^3 * y + y^3 * z + z^3 * x ≤ V)   :=  by sorry
