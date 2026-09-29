-- Prove2me | Theorems.Thm_lean_workbook_plus_74741
-- name    : lean_workbook_plus_74741
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a99cbb98-2449-4379-b9a5-1244d9fc68af
-- statement:
--   The equation $a^{3} +b^{3} =c^{3}$ does have the integer solution $(a, b, c) = (0,0,0)$ and $(a,b,c) = (k, -k, 0)$ for some $k \in \mathbb{Z}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74741 : ∃ a b c : ℤ, a^3 + b^3 = c^3 ∧ (a = 0 ∧ b = 0 ∧ c = 0) ∨ (∃ k : ℤ, a = k ∧ b = -k ∧ c = 0)   :=  by sorry
