-- Prove2me | Theorems.Thm_lean_workbook_plus_5951
-- name    : lean_workbook_plus_5951
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/1fc353d7-fc67-47a2-80ad-16982b98ea8e
-- statement:
--   $ =\allowbreak \ln \frac{\sqrt{3}+1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5951 :
  (Real.log (Real.sqrt 3 + 1) - Real.log 2) = Real.log ((Real.sqrt 3 + 1) / 2)   :=  by sorry
