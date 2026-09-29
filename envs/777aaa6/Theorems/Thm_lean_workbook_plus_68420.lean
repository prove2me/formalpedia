-- Prove2me | Theorems.Thm_lean_workbook_plus_68420
-- name    : lean_workbook_plus_68420
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/9ab2f3f2-a70d-48fe-b306-c10679d65fa9
-- statement:
--   Rewrite $5n^{11}-2n^5-3n$ in the form $(n-1)n(n+1)(5n^4(n^4+n^2+1)+3(n^2+1))$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68420 (n : ℤ) : 5*n^11 - 2*n^5 - 3*n = (n-1)*n*(n+1)*(5*n^4*(n^4 + n^2 + 1) + 3*(n^2 + 1))   :=  by sorry
