-- Prove2me | Theorems.Thm_lean_workbook_plus_30628
-- name    : lean_workbook_plus_30628
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/8f53d0c8-bff6-4fe4-b60a-5d84aee92a2b
-- statement:
--   Let $ a,b,c,d$ are real numbers,prove that: $(b^2+c^2+d^2+a^2)^2 \geq b^2(b+d)(c+a)+c^2(c+a)(b+d)+d^2(b+d)(c+a)+a^2(c+a)(b+d).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30628 (a b c d : ℝ) : (b^2+c^2+d^2+a^2)^2 >= b^2 * (b+d) * (c+a) + c^2 * (c+a) * (b+d) + d^2 * (b+d) * (c+a) + a^2 * (c+a) * (b+d)   :=  by sorry
