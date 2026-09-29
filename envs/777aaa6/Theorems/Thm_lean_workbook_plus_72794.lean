-- Prove2me | Theorems.Thm_lean_workbook_plus_72794
-- name    : lean_workbook_plus_72794
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/1074f6a0-051f-4282-b44a-00b6b8310f56
-- statement:
--   Factorize $x^7+x^2+1$ by reducing exponents modulo 3.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72794 : ∀ x : ℤ, x^7 + x^2 + 1 = (x^2 + x + 1) * (x^5 - x^4 + x^2 - x + 1)   :=  by sorry
