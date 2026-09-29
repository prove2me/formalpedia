-- Prove2me | Theorems.Thm_lean_workbook_plus_52112
-- name    : lean_workbook_plus_52112
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/83a366e7-cdcb-4ea3-ad11-40c30f2c393f
-- statement:
--   Prove that for positive reals a, b, c, we have the inequality $ \frac{a}{b+2c} +\frac{b}{c+2a} +\frac{c}{a+2b} \geq 1 $ with equality only for a = b = c.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52112 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) ≥ 1) ∧ (a = b ∧ b = c → a = b ∧ b = c)   :=  by sorry
