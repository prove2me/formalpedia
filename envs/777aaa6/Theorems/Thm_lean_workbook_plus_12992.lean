-- Prove2me | Theorems.Thm_lean_workbook_plus_12992
-- name    : lean_workbook_plus_12992
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/39cedf98-92f1-428a-88a2-edb72ac9cbf2
-- statement:
--   Calculate the integer part of this sum: $\lfloor 1+{\sqrt{2}}+{\sqrt{3}}+.....+{\sqrt{100}} \rfloor$. P. S. $\lfloor x \rfloor$ is integer part of $x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12992 ∑ k in Finset.range 100, ⌊Real.sqrt k⌋ = 671   :=  by sorry
