-- Prove2me | Theorems.Thm_lean_workbook_plus_67988
-- name    : lean_workbook_plus_67988
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/12ad4c32-e00a-4194-b46b-70681fd36e20
-- statement:
--   Prove that if $a+b+c=0$ then \n\n $2(a^5+b^5+c^5)=5abc(a^2+b^2+c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67988 (a b c : ℂ) (hab : a + b + c = 0) : 2 * (a^5 + b^5 + c^5) = 5 * a * b * c * (a^2 + b^2 + c^2)   :=  by sorry
