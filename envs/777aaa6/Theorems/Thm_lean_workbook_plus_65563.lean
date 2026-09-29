-- Prove2me | Theorems.Thm_lean_workbook_plus_65563
-- name    : lean_workbook_plus_65563
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/de570705-1773-44ab-b841-7f916492f3f8
-- statement:
--   What is the greatest number n that works for $2^n$ so that $2^n$ is a factor of 100! ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65563 :
  IsGreatest {n : ℕ | 2 ^ n ∣ 100! } 9   :=  by sorry
