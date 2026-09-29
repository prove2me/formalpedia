-- Prove2me | Theorems.Thm_lean_workbook_plus_9397
-- name    : lean_workbook_plus_9397
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/73616d2b-2b66-4893-a0ce-355d1eacf097
-- statement:
--   Let $a,b,c$ are real numbers,prove that: $(a^3+b^3+c^3)(a+b+c)\geq (ab+bc+ac)(a^2+b^2+c^2).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9397 (a b c : ℝ) : (a ^ 3 + b ^ 3 + c ^ 3) * (a + b + c) ≥ (a * b + b * c + a * c) * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
