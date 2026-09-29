-- Prove2me | Theorems.Thm_lean_workbook_plus_22580
-- name    : lean_workbook_plus_22580
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/7cb4b4a1-74bc-4df5-af50-0c1907c6b0b8
-- statement:
--   For any $m<n$ , $\binom{n}{m+1}=\frac{n-m}{m+1}\binom{n}{m}$ , so $\binom{n}{m+1}<\binom{n}{m}$ if $m<\frac{n-1}2$ and $\binom{n}{m+1}>\binom{n}{m}$ if $m>\frac{n-1}2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22580 (n m : ℕ) (h₁ : m < n) (h₂ : m < (n - 1) / 2) :
  (n.choose (m + 1)) < (n.choose m)   :=  by sorry
