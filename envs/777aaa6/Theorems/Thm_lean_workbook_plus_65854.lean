-- Prove2me | Theorems.Thm_lean_workbook_plus_65854
-- name    : lean_workbook_plus_65854
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ec662b77-fd7c-496a-b82d-2a03c011c25d
-- statement:
--   Given the triangle inequality: $ a+b\ge c$, $ b+c\ge a$, $ c+a\ge b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65854 {a b c : ℝ} (hx: a + b >= c) (hb: b + c >= a) (hc: a + c >= b) : a + b >= c ∧ b + c >= a ∧ a + c >= b   :=  by sorry
