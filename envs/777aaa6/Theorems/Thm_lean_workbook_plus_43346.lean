-- Prove2me | Theorems.Thm_lean_workbook_plus_43346
-- name    : lean_workbook_plus_43346
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/bce929e9-523e-4f57-8231-a8933bbb46c9
-- statement:
--   $ \frac{1}{k^2-1} = \frac{1}{2} \left ( \frac{1}{k-1} - \frac{1}{k+1} \right ) \neq \frac {1}{k - 1} - \frac {1}{k}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43346  (k : ℂ)
  (h₀ : k ≠ 1)
  (h₁ : k ≠ -1) :
  1 / (k^2 - 1) = 1 / 2 * (1 / (k - 1) - 1 / (k + 1))   :=  by sorry
