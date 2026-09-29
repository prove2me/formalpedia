-- Prove2me | Theorems.Thm_lean_workbook_plus_6938
-- name    : lean_workbook_plus_6938
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e134c83d-8443-4168-936f-457c059dd695
-- statement:
--   Prove that $\sum _{x=1} ^{26} x(53-x) = \sum_{x=1}^{26} 53x - \sum_{x=1} ^{26}x^2=12402$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6938 :
  ∑ x in Finset.Icc 1 26, (x * (53 - x)) = ∑ x in Finset.Icc 1 26, (53 * x) - ∑ x in Finset.Icc 1 26, (x ^ 2)   :=  by sorry
