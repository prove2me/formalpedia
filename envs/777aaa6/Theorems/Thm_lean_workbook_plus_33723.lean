-- Prove2me | Theorems.Thm_lean_workbook_plus_33723
-- name    : lean_workbook_plus_33723
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/540a64e0-d5a9-474e-825a-4dde0e346e3f
-- statement:
--   $\binom{100}{50}=\frac{100!}{50!50!}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33723 (h₁ : 100 > 50) : choose 100 50 = 100! / (50! * 50!)   :=  by sorry
