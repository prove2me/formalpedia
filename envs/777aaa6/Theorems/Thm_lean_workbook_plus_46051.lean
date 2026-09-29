-- Prove2me | Theorems.Thm_lean_workbook_plus_46051
-- name    : lean_workbook_plus_46051
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ed0739be-5ba4-43e7-8abb-6725586492f1
-- statement:
--   Alternatively, let $ AB = 2x$ . If $ M$ is the mid-point of $ AB$ and $ PM = d$ , then $ \tan 15 = \frac{d}{x}$ , so $ d=x\tan 15$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46051  (x d : ℝ)
  (h₀ : 0 < x ∧ 0 < d)
  (h₁ : Real.tan 15 = d / x) :
  d = x * Real.tan 15   :=  by sorry
