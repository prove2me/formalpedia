-- Prove2me | Theorems.Thm_lean_workbook_plus_14861
-- name    : lean_workbook_plus_14861
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/79a1ce46-446f-4e74-b30b-efb5d114bfc3
-- statement:
--   Prove that for $a, b, c, d > 0$, \n $ (a+b+c+d)(abc+bcd+cda+dab)\le (a+b)(a+c)(b+d)(c+d) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14861 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b) ≤ (a + b) * (a + c) * (b + d) * (c + d)   :=  by sorry
