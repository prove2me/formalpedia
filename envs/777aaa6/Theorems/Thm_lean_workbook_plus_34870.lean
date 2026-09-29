-- Prove2me | Theorems.Thm_lean_workbook_plus_34870
-- name    : lean_workbook_plus_34870
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/9fd304cc-5ac6-4dc5-8653-c904d521d0be
-- statement:
--   Given $a+b=1$ , prove the inequality $a^2+b^2>ab$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34870 (a b : ℝ) (h : a + b = 1) : a^2 + b^2 > a * b   :=  by sorry
