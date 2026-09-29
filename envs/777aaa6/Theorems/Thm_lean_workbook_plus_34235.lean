-- Prove2me | Theorems.Thm_lean_workbook_plus_34235
-- name    : lean_workbook_plus_34235
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/8d186491-476a-401e-a393-4d3cc978fe8e
-- statement:
--   Prove that for positive real numbers $a$, $b$, and $c$, the inequality $(a+b)(b+c)(c+a) \ge \frac{8}{9}(a+b+c)(ab+bc+ca)$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34235 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) * (b + c) * (c + a) ≥ (8:ℝ) / 9 * (a + b + c) * (a * b + b * c + c * a)   :=  by sorry
