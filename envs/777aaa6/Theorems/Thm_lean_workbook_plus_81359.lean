-- Prove2me | Theorems.Thm_lean_workbook_plus_81359
-- name    : lean_workbook_plus_81359
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/a980cf23-f388-4674-aab8-5358ec2daa7f
-- statement:
--   For the first one, note that\n\n $\sum_{k=1}^{n-1}(1+\ln k)=n-1+\ln((n-1)!)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81359 ∀ n, ∑ k in Finset.range (n-1), (1 + Real.log k) = n-1 + Real.log (n-1)!   :=  by sorry
