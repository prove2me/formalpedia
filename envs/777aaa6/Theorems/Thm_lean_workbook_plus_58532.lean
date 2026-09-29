-- Prove2me | Theorems.Thm_lean_workbook_plus_58532
-- name    : lean_workbook_plus_58532
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/aff6a541-768c-4f01-a01a-f9a7dd8f37d6
-- statement:
--   $\iff c(c+a)+b(a+b)=(a+b)(c+a) \iff a^2=b^2+c^2-bc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58532 : ∀ a b c : ℝ, c * (c + a) + b * (a + b) = (a + b) * (c + a) ↔ a^2 = b^2 + c^2 - b * c   :=  by sorry
