-- Prove2me | Theorems.Thm_lean_workbook_plus_3911
-- name    : lean_workbook_plus_3911
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/64e51252-ca3c-49af-80d8-976271f585c2
-- statement:
--   $a^3+b^3+c^3-3abc=(a+b+c)(a^2+b^2+c^2)-\sum_{cyc} (a^2b+b^2a) - 3abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3911 : ∀ a b c : ℝ, a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c)*(a^2 + b^2 + c^2) - (a^2*b + b^2*a + a^2*c + c^2*a + b^2*c + c^2*b) - 3*a*b*c   :=  by sorry
