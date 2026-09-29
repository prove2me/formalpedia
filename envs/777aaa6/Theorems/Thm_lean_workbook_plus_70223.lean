-- Prove2me | Theorems.Thm_lean_workbook_plus_70223
-- name    : lean_workbook_plus_70223
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/9987ca09-d1da-474c-867a-80efd8fb307d
-- statement:
--   (#1) $n+d=70$ \n(#2) $5n+10d=555$ \n(#3)=5*(#1) $5n+5d=350$ \n(#4)=(#2)-(#3) $5d=205$ \n(#5)=(#4)/5 $d=41$ \n(#6)=(#1)-(#5) $n=29$ \n(#7)=(#5)-(#6) $d-n=\boxed{12}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70223  (n d : ℕ)
  (h₀ : n + d = 70)
  (h₁ : 5 * n + 10 * d = 555)
  (h₂ : 5 * n + 5 * d = 350)
  (h₃ : 5 * d = 205)
  (h₄ : d = 41)
  (h₅ : n = 29)
  (h₆ : d - n = 12) :
  d - n = 12   :=  by sorry
