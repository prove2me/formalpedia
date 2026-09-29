-- Prove2me | Theorems.Thm_lean_workbook_plus_34615
-- name    : lean_workbook_plus_34615
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/0e7c16bd-6ab5-4f16-b21d-d8fde40bf3e8
-- statement:
--   $ (\frac {1}{2} \cdot \frac {3}{4} \cdot \frac {5}{6} \cdot ... \cdot \frac {1997}{1998})^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34615 : (∏ i in Finset.Icc 1 1998, ((2 * i - 1) / (2 * i)))^2 = (∏ i in Finset.Icc 1 1998, ((2 * i - 1) / (2 * i))) * (∏ i in Finset.Icc 1 1998, ((2 * i - 1) / (2 * i)))   :=  by sorry
