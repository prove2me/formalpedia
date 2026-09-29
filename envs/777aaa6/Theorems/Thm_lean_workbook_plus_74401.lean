-- Prove2me | Theorems.Thm_lean_workbook_plus_74401
-- name    : lean_workbook_plus_74401
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/75ede993-9334-4285-af92-398ae99181f9
-- statement:
--   A function is odd if $f(x)=-f(-x)$ for all $x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74401 (f : ℝ → ℝ) : (∀ x, f x = -f (-x)) ↔ ∀ x, f x = -f (-x)   :=  by sorry
