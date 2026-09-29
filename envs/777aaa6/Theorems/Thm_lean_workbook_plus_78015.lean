-- Prove2me | Theorems.Thm_lean_workbook_plus_78015
-- name    : lean_workbook_plus_78015
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/07451695-0fbf-41d2-93ce-404653489d2f
-- statement:
--   If $ \cos \alpha=\frac{60} {61}, 0\le \alpha \le \frac{\pi} {2}$, find the exact value of $ \sin{\frac{\alpha} {2}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78015 (α : ℝ) (h₁ : 0 ≤ α) (h₂ : α ≤ π/2) (h₃ : cos α = 60/61) : sin (α/2) = √122 / 122   :=  by sorry
