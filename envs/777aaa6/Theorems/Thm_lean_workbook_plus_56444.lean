-- Prove2me | Theorems.Thm_lean_workbook_plus_56444
-- name    : lean_workbook_plus_56444
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/af70a932-861e-4607-b249-87c64fef36a1
-- statement:
--   Now working backwords, we have the following list of numbers: $ 7223$ $ 7223 - 84^2 = 167$ $ 167 - 12^2 = 23$ $ 23 - 4^2 = 7$ $ 7 - 2^2 = 3$ $ 3 - 1^2 = 2$ $ 2 - 1^2 = 1$ $ 1 - 1^2 = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56444  (a b c d e f g h : ℕ)
  (h₀ : a = 7223)
  (h₁ : b = a - 84^2)
  (h₂ : c = b - 12^2)
  (h₃ : d = c - 4^2)
  (h₄ : e = d - 2^2)
  (h₅ : f = e - 1^2)
  (h₆ : g = f - 1^2)
  (h₇ : h = g - 1^2) :
  h = 0   :=  by sorry
