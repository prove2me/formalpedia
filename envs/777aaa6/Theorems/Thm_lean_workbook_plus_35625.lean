-- Prove2me | Theorems.Thm_lean_workbook_plus_35625
-- name    : lean_workbook_plus_35625
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/29db0eef-f3f9-4906-99cf-f3bc32e43c27
-- statement:
--   Let a,b,c>0. Prove that: $ P=\frac{1}{2(a+b)}+\frac{1}{3(b+c)}+\frac{1}{6(c+a)}\geq \frac{6}{4a+5b+3c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35625 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (2 * (a + b)) + 1 / (3 * (b + c)) + 1 / (6 * (c + a)) ≥ 6 / (4 * a + 5 * b + 3 * c)   :=  by sorry
