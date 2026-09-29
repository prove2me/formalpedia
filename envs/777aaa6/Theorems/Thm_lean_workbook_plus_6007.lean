-- Prove2me | Theorems.Thm_lean_workbook_plus_6007
-- name    : lean_workbook_plus_6007
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f6f61f5f-d582-4a0b-9c80-6c3a0ab1dfab
-- statement:
--   Let $n=x+19$ \n\n Then: \n\n $n*(n+1)*(n+2)*(n+3) = $ \n\n $=> (n*(n+3))*((n+1)*(n+2))=$ \n\n $=> (n^2+3n)*(n^2+3n+2)=$ \n\n $=> (n^2+3n)^2+ 2*(n^2+3n)=$ \n\n $=> (n^2+3n)^2+2*(n^2+3n)+1-1 = $ \n\n $=> (n^2+3n+1)^2 - 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6007  (x : ℕ)
  (n : ℕ)
  (h₀ : n = x + 19) :
  n * (n + 1) * (n + 2) * (n + 3) = (n^2 + 3 * n + 1)^2 - 1   :=  by sorry
