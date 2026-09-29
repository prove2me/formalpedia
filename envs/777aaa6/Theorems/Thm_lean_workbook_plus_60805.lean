-- Prove2me | Theorems.Thm_lean_workbook_plus_60805
-- name    : lean_workbook_plus_60805
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/0b44f6c2-1202-41b9-864b-4f8de17ecab4
-- statement:
--   Then, if $ b>0$ , we have $ b^2<b^2+b+1<(b+1)^2$ and $ b^2+b+1$ can't be a perfect square. \n\nSame, if $ b<-1$ , we have $ (b+1)^2<b^2+b+1<b^2$ and $ b^2+b+1$ can't be a perfect square.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60805  (b : ℤ)
  (h₀ : 0 < b)
  (h₁ : b^2 + b + 1 = x^2) :
  False   :=  by sorry
