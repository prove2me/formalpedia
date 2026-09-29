-- Prove2me | Theorems.Thm_lean_workbook_plus_78689
-- name    : lean_workbook_plus_78689
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/5ac617f1-ee84-4ac3-a9c3-5e042af87a65
-- statement:
--   If $n$ is odd, prove that $3 \nmid 2^n - 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78689 (n : ℕ) (h : n % 2 = 1) : ¬ 3 ∣ (2^n - 1)   :=  by sorry
