-- Prove2me | Theorems.Thm_lean_workbook_plus_35511
-- name    : lean_workbook_plus_35511
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/ba05ca20-c3f8-42f1-a618-e4d18da9d4fd
-- statement:
--   Let $a,b$ are non-negative real numbers such that $a+b=ab+1.$ Prove that $a^2 +b^2 \geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35511 (a b : ℝ) (h : a + b = a * b + 1) : a ^ 2 + b ^ 2 ≥ 1   :=  by sorry
