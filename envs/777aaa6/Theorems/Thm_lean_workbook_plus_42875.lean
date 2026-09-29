-- Prove2me | Theorems.Thm_lean_workbook_plus_42875
-- name    : lean_workbook_plus_42875
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/cf784375-0246-473b-806e-f34b023cbecc
-- statement:
--   Equality holds for $a=b=c=\frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42875 (a b c : ℝ) : (a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 ∧ (a = b ∧ b = c ∧ c = 3 / 2)) ↔ a = b ∧ b = c ∧ c = 3 / 2   :=  by sorry
