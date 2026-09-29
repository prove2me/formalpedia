-- Prove2me | Theorems.Thm_lean_workbook_plus_45324
-- name    : lean_workbook_plus_45324
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/330b3bd3-589a-473c-aef0-365cc64b6b6b
-- statement:
--   We have to prove that: $(a^2+b^2+c^2)^2 \geq (a+b+c)[ab(a+b)+bc(b+c)+ca(c+a)-3abc]$ $\Leftrightarrow$ $a^4+b^4+c^4+abc(a+b+c) \geq bc(b^2+c^2) + ca(c^2+a^2) + ab(a^2+b^2)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45324 (a b c: ℝ) : (a^2+b^2+c^2)^2 ≥ (a+b+c)*(a*b*(a+b) + b*c*(b+c) + c*a*(c+a) - 3*a*b*c) ↔ a^4+b^4+c^4+(a*b*c)*(a+b+c) ≥ b*c*(b^2+c^2) + c*a*(c^2+a^2) + a*b*(a^2+b^2)   :=  by sorry
