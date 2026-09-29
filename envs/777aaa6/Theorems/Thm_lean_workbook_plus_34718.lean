-- Prove2me | Theorems.Thm_lean_workbook_plus_34718
-- name    : lean_workbook_plus_34718
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/acc4dae6-7b29-42c4-9f04-49279b9670d4
-- statement:
--   Is it true that $i = \sqrt{-1}$ implies $i^4 = 1$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34718  (q e : ℂ)
  (h₀ : q = Complex.I)
  (h₁ : e = 4) :
  q^e = 1   :=  by sorry
