-- Prove2me | Theorems.Thm_lean_workbook_plus_37227
-- name    : lean_workbook_plus_37227
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/f93e08bc-14aa-4745-bc18-bcdf9c968feb
-- statement:
--   If $a_{n}< b_{n}$ for all $n$ , and the sums of the two sequences converge, then $\sum a_{n}< \sum b_{n}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37227 (ι : Type*) (a b : ι → ℝ) (h₁ : Nonempty ι) (h₂ : ∀ n, a n < b n) (h₃ : Summable a) (h₄ : Summable b) : ∑' n, a n < ∑' n, b n   :=  by sorry
