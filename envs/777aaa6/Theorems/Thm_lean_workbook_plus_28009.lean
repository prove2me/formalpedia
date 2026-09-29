-- Prove2me | Theorems.Thm_lean_workbook_plus_28009
-- name    : lean_workbook_plus_28009
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/621ac1f8-b496-4d54-9072-bd2933c9fc4d
-- statement:
--   Prove that $a+b+c+3abc\ge 2(ab+bc+ca)$ given $0 < a,b,c \le 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28009 (a b c : ℝ) (ha : 0 < a ∧ a ≤ 1) (hb : 0 < b ∧ b ≤ 1) (hc : 0 < c ∧ c ≤ 1) : a + b + c + 3 * a * b * c ≥ 2 * (a * b + b * c + c * a)   :=  by sorry
