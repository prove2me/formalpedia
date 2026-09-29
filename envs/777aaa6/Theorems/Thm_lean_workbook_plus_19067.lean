-- Prove2me | Theorems.Thm_lean_workbook_plus_19067
-- name    : lean_workbook_plus_19067
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/76fe0d32-f225-46c5-820d-2ca94e17b8f2
-- statement:
--   Find an exact value to $S=\frac{({{2}^{3}}-1)\times ({{3}^{3}}-1)\times ...\times ({{100}^{3}}-1)}{({{2}^{3}}+1)\times ({{3}^{3}}+1)\times ...\times ({{100}^{3}}+1)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19067 : (∏ i in Finset.Icc 2 100, (i^3 - 1)) / (∏ i in Finset.Icc 2 100, (i^3 + 1)) = 3367 / 5050   :=  by sorry
