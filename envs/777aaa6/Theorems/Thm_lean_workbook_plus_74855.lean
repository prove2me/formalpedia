-- Prove2me | Theorems.Thm_lean_workbook_plus_74855
-- name    : lean_workbook_plus_74855
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d9192149-dcda-45de-9a87-bf84132396a5
-- statement:
--   Find the last two digits of the number: $(11 + 12 + 13 +...+ 2006)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74855 : (∑ k in Finset.Icc 11 2006, k)^2 ≡ 56 [MOD 100]   :=  by sorry
