-- Prove2me | Theorems.Thm_lean_workbook_plus_34171
-- name    : lean_workbook_plus_34171
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/7f152dbb-4b80-4f53-a649-4bdbe9861869
-- statement:
--   Given $w:=\sin(C)$, prove that $w(1-w) \leq \frac{1}{4}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34171 : ∀ C : ℝ, sin C * (1 - sin C) ≤ 1 / 4   :=  by sorry
