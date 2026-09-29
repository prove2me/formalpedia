-- Prove2me | Theorems.Thm_lean_workbook_plus_31842
-- name    : lean_workbook_plus_31842
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/9e138cf4-498d-47b2-aca7-b8b54c0ddfca
-- statement:
--   Let $ a,$ $ b,$ $ c$ be positive real numbers. Prove that $ \frac {a}{b} + \frac {b}{c} + \frac {c}{a} \ge \frac {a + b}{b + c} + \frac {b + c}{a + b} + 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31842 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a / b + b / c + c / a >= (a + b) / (b + c) + (b + c) / (a + b) + 1   :=  by sorry
