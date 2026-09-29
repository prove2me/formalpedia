-- Prove2me | Theorems.Thm_lean_workbook_plus_28720
-- name    : lean_workbook_plus_28720
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/395c65cf-1bd5-43e7-8711-3131917380b6
-- statement:
--   All number = $\frac{11!}{7! \cdot 4!} + \frac{9!}{5! \cdot 4!} + \frac{7!}{3! \cdot 4!} + \frac{5!}{1! \cdot 4!}=496$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28720 :
  11! / (7! * 4!) + 9! / (5! * 4!) + 7! / (3! * 4!) + 5! / (1! * 4!) = 496   :=  by sorry
