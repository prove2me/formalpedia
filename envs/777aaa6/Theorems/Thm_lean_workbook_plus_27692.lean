-- Prove2me | Theorems.Thm_lean_workbook_plus_27692
-- name    : lean_workbook_plus_27692
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/0b006628-c357-4435-bd41-a51cd04d0e45
-- statement:
--   The following identity holds, for any three real numbers $a$ , $b$ and $c$ :\n\n $(a^2+b^2)(b^2+c^2)(c^2+a^2)=(ab^2+bc^2+ca^2-a b c)^2+(a^2b+b^2c+c^2a-abc)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27692 : ∀ a b c : ℝ, (a^2+b^2)*(b^2+c^2)*(c^2+a^2) = (ab^2+bc^2+ca^2-(a*b*c))^2 + (a^2*b+b^2*c+c^2*a-(a*b*c))^2   :=  by sorry
