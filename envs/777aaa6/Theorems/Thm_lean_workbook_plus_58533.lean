-- Prove2me | Theorems.Thm_lean_workbook_plus_58533
-- name    : lean_workbook_plus_58533
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/8fef0656-321d-4bc8-88eb-18327cb17707
-- statement:
--   If $xp(x) = yp(y)$ holds for ALL integers, then $p(1) = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58533 (p : ℤ → ℤ) (h : ∀ x y : ℤ, x * p x = y * p y) : p 1 = 0   :=  by sorry
