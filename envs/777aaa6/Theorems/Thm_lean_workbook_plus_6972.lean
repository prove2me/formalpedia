-- Prove2me | Theorems.Thm_lean_workbook_plus_6972
-- name    : lean_workbook_plus_6972
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4e6f1cec-c7e8-4248-a2ec-eee48e474dd0
-- statement:
--   Take $k=x+50$ . \n\n$$(k-49)^2 + (k-48)^2 + \dots + (k+49)^2 = 99k^2 + 2 \left( 1^2 + 2^2 + \dots + 49^2 \right) = 99k^2 + \dfrac{2}{3} \cdot 49 \cdot 50 \cdot 99 = 99k^2 + 33 \cdot 49 \cdot 100$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6972 :
  ∑ i in Finset.Icc (-49) 49, (i + 50)^2 = 99 * (x + 50)^2 + 33 * 49 * 100   :=  by sorry
