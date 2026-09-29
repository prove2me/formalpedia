-- Prove2me | Theorems.Thm_lean_workbook_plus_33770
-- name    : lean_workbook_plus_33770
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/aa053806-1d1b-4e40-b2ff-292172584334
-- statement:
--   Prove that: \n\n $(a - b)(a - c)(a - d)(b - c)(b - d)(c - d) \le 27$ \n\n P.S:Equality is held when \n\n $a = 4{\cos ^2}10,b = 4{\cos ^2}50,c = 4{\cos ^2}70,d = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33770 : ∀ a b c d : ℝ, (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) ≤ 27   :=  by sorry
