-- Prove2me | Theorems.Thm_lean_workbook_plus_3749
-- name    : lean_workbook_plus_3749
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/2bb1900a-9629-4e20-9660-7ab31f725322
-- statement:
--   Which number is larger, $A$ or $B$ , where \n\n $A = \dfrac{1}{2015} (1 + \dfrac12 + \dfrac13 + \cdots + \dfrac{1}{2015})$ and \n\n $B = \dfrac{1}{2016} (1 + \dfrac12 + \dfrac13 + \cdots + \dfrac{1}{2016})$ ? Prove your answer is correct.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3749 : (1/2015)*(∑i in Finset.range 2015, 1/(i+1)) > (1/2016)*(∑i in Finset.range 2016, 1/(i+1))   :=  by sorry
