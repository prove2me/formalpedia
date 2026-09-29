-- Prove2me | Theorems.Thm_lean_workbook_plus_31978
-- name    : lean_workbook_plus_31978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b72e8cc2-c723-476c-b5aa-6b592062c0a1
-- statement:
--   By AM-GH having $\frac{1}{ab}+\frac{1}{bc}+\frac{1}{ca} \ge \frac{9}{ab+bc+ca}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31978 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) ≥ 9 / (a * b + b * c + c * a)   :=  by sorry
