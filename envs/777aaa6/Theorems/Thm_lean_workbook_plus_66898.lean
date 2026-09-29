-- Prove2me | Theorems.Thm_lean_workbook_plus_66898
-- name    : lean_workbook_plus_66898
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/335e6106-7f09-47c6-b997-340e23777193
-- statement:
--   We can rewrite $\log_{4} 6$ as $\log_{2} \sqrt{6}$ . This works as if we write $\log_{4} 6=x$ , then $4^x=6$ . Taking the square root, $2^x=\sqrt{6}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66898 :
  Real.logb 4 6 = Real.logb 2 (Real.sqrt 6)   :=  by sorry
