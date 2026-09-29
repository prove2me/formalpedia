-- Prove2me | Theorems.Thm_lean_workbook_plus_63747
-- name    : lean_workbook_plus_63747
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/313b5820-b85e-4486-8f26-f73c0e4587b6
-- statement:
--   And so $a=c=d=\frac 252013$ and $b=e=f=\frac 352013$ and sum os squares of edges is $\frac 652013^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63747  (a b c d e f : ℝ)
  (h₀ : a = 2 / 5 * 2013)
  (h₁ : b = 3 / 5 * 2013)
  (h₂ : c = 2 / 5 * 2013)
  (h₃ : d = 2 / 5 * 2013)
  (h₄ : e = 3 / 5 * 2013)
  (h₅ : f = 3 / 5 * 2013) :
  a^2 + b^2 + c^2 + d^2 + e^2 + f^2 = 6 / 5 * 2013^2   :=  by sorry
