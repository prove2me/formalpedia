-- Prove2me | Theorems.Thm_lean_workbook_plus_53422
-- name    : lean_workbook_plus_53422
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/1ebbb568-2c8b-4a50-8aa6-e352f1f829c5
-- statement:
--   Let $0 \le a,b,c \le 1.$ Prove that $2(a+b+c)-ab-bc-ca\leq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53422 (a b c : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) : 2 * (a + b + c) - a * b - b * c - c * a ≤ 3   :=  by sorry
