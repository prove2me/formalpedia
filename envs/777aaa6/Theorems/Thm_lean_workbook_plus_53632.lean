-- Prove2me | Theorems.Thm_lean_workbook_plus_53632
-- name    : lean_workbook_plus_53632
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/31e25cd6-12a1-4c04-bf17-993adaba56d4
-- statement:
--   Prove the inequality $\frac{(a+b)(b+c)(c+a)}{8} \geq \frac{(a+b+c)(ab+bc+ca)}{9}$ for positive numbers $a, b, c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53632 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) * (b + c) * (c + a) / 8 ≥ (a + b + c) * (a * b + b * c + c * a) / 9   :=  by sorry
