-- Prove2me | Theorems.Thm_lean_workbook_plus_10999
-- name    : lean_workbook_plus_10999
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/08ab86bc-1cd4-470a-b299-cb4829c25be9
-- statement:
--   If a,b,c are positive integers and $a+b+c=1$ prove that $5(a^{2}+b^{2}+c^{2})\leq 6(a^{3}+b^{3}+c^{3})+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10999 (a b c : ℕ) (hab : a + b + c = 1) : 5 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 6 * (a ^ 3 + b ^ 3 + c ^ 3) + 1   :=  by sorry
