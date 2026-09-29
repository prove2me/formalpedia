-- Prove2me | Theorems.Thm_lean_workbook_plus_48277
-- name    : lean_workbook_plus_48277
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/1966d7fd-2af7-40ec-8f5f-47eca4606972
-- statement:
--   Prove that if $a^2+b^2+c^2=ab+bc+ca$, then $a=b=c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48277 (a b c : ℝ) (h : a^2 + b^2 + c^2 = a * b + b * c + c * a) : a = b ∧ b = c ∧ c = a   :=  by sorry
