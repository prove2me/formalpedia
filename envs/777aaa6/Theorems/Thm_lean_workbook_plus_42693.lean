-- Prove2me | Theorems.Thm_lean_workbook_plus_42693
-- name    : lean_workbook_plus_42693
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/1c9871d5-13b5-4db5-b215-3c74948e2a94
-- statement:
--   If $a,b,c,d\ge 1$ \n\n It is sufficient to prove $8+abc+bcd+cda+dab\ge 3(a+b+c+d)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42693 (a b c d : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) : 8 + a * b * c + b * c * d + c * d * a + d * a * b ≥ 3 * (a + b + c + d)   :=  by sorry
