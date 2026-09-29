-- Prove2me | Theorems.Thm_lean_workbook_plus_7664
-- name    : lean_workbook_plus_7664
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/984faa77-1ef2-4ce4-aa5d-c70a71d1d582
-- statement:
--   Prove that for real numbers $a, b, c$,\n\n $$|a+b| + |b+c| + |c+a| \le |a|+|b|+|c| + |a+b+c|.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7664 (a b c : ℝ) : |a + b| + |b + c| + |c + a| ≤ |a| + |b| + |c| + |a + b + c|   :=  by sorry
