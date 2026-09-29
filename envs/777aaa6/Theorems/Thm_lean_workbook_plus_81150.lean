-- Prove2me | Theorems.Thm_lean_workbook_plus_81150
-- name    : lean_workbook_plus_81150
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/126571f4-de30-45af-955c-2fc68d29a5ea
-- statement:
--   Let $a,b,c,$ real numbers such that: \n\n $$ab<c^2$$ \n$$bc<a^2$$ \n$$ac<b^2$$ Prove that: \n$$ab+bc+ca<0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81150 (a b c : ℝ) (h1 : a * b < c ^ 2) (h2 : b * c < a ^ 2) (h3 : a * c < b ^ 2) : a * b + b * c + c * a < 0   :=  by sorry
