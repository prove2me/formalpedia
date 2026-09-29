-- Prove2me | Theorems.Thm_lean_workbook_plus_48637
-- name    : lean_workbook_plus_48637
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/9c73c3bb-82b2-4143-adfe-9589d0ab412e
-- statement:
--   Prove that $\frac{1}{ab(a+b)+abc}+\frac{1}{bc(b+c)+abc}+\frac{1}{ac(a+c)+abc}=\frac{1}{ab(a+b+c)}+\frac{1}{bc(a+b+c)}+\frac{1}{ac(a+b+c)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48637 (a b c : ℝ) : (1 / (a * b * (a + b) + a * b * c)) + (1 / (b * c * (b + c) + a * b * c)) + (1 / (a * c * (a + c) + a * b * c)) = (1 / (a * b * (a + b + c))) + (1 / (b * c * (a + b + c))) + (1 / (a * c * (a + b + c)))   :=  by sorry
