-- Prove2me | Theorems.Thm_lean_workbook_plus_52749
-- name    : lean_workbook_plus_52749
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/6b9afeaa-b787-4541-800f-41789d70000d
-- statement:
--   Prove that (2m+3-2k)(2m+3+2k)=9 given $m^2+3m=k^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52749 (m k : ℤ) (h₁ : m^2 + 3*m = k^2) : (2*m + 3 - 2*k) * (2*m + 3 + 2*k) = 9   :=  by sorry
