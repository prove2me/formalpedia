-- Prove2me | Theorems.Thm_lean_workbook_plus_6188
-- name    : lean_workbook_plus_6188
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/31641f79-83d7-44fb-ba51-cee1c6d01811
-- statement:
--   If $a \mid b$, prove that $a \mid a+b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6188 {a b : ℤ} (h : a ∣ b) : a ∣ a + b   :=  by sorry
