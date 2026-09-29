-- Prove2me | Theorems.Thm_lean_workbook_plus_22619
-- name    : lean_workbook_plus_22619
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/20ebe8ba-e58c-4154-93d4-fc489a0f40c3
-- statement:
--   By induction principle, it is not difficult to prove that \n\n $$(n-2)<\\frac{n!}{\\sum^{n-1}_{r=1}r!}<(n-1)\\,\\,\\forall\\,\\,n\\ge 4,\\,n\\in\\mathbb{N}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22619 (n : ℕ) (hn : 4 ≤ n) :
  (n - 2) < (n! / ∑ r in Finset.Ico 1 (n - 1), r!) ∧
  (n! / ∑ r in Finset.Ico 1 (n - 1), r!) < (n - 1)   :=  by sorry
