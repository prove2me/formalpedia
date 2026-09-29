-- Prove2me | Theorems.Thm_lean_workbook_plus_75550
-- name    : lean_workbook_plus_75550
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/8856472f-c028-4162-9172-dce27fdc75bb
-- statement:
--   Prove that \n\n(i) $ \sum_{k=1}^{n} \frac{1}{k} > \ln (n+1)$ , \n\n(ii) $\sum_{k=1}^{\infty} \frac{1}{k^{2}} < 1 + \ln 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75550 : ∀ n : ℕ, (∑ k in Finset.Icc 1 n, (1 : ℝ) / k) > Real.log (n + 1) ∧ (∑' k : ℕ, (1 : ℝ) / k^2) < 1 + Real.log 2   :=  by sorry
