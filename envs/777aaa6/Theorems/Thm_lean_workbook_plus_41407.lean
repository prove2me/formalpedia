-- Prove2me | Theorems.Thm_lean_workbook_plus_41407
-- name    : lean_workbook_plus_41407
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/ef8fb515-6f1c-427c-927f-97fcc12d6f7a
-- statement:
--   Let $0 \le a,b,c \le 1.$ Prove that $3(a+b+c)-ab-bc-ca\leq 6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41407 (a b c : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1): 3 * (a + b + c) - a * b - b * c - c * a ≤ 6   :=  by sorry
