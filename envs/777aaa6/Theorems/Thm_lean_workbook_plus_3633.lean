-- Prove2me | Theorems.Thm_lean_workbook_plus_3633
-- name    : lean_workbook_plus_3633
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/712f7ba9-7b71-431a-a316-4ce774dda246
-- statement:
--   Find: $a^2(b+c) + b^2(a+c) + c^2(a+b)$ if $a+b+c=6$ , $a^2+b^2+c^2=40$ , and $a^3+b^3+c^3=200$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3633 (a b c : ℝ) (h₁ : a + b + c = 6) (h₂ : a ^ 2 + b ^ 2 + c ^ 2 = 40) (h₃ : a ^ 3 + b ^ 3 + c ^ 3 = 200) : a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b) = 40   :=  by sorry
