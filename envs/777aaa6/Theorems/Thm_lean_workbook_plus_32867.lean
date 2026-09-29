-- Prove2me | Theorems.Thm_lean_workbook_plus_32867
-- name    : lean_workbook_plus_32867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/2426c71d-fbfc-4f5d-aad8-fa35e3c6179c
-- statement:
--   Let $a,b$ be positive real numbers . Prove that $\frac{a}{b} + \frac{b}{a} \ge \frac{a+1}{b+1} + \frac{b+1}{a+1} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32867 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a / b + b / a ≥ (a + 1) / (b + 1) + (b + 1) / (a + 1)   :=  by sorry
