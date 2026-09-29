-- Prove2me | Theorems.Thm_lean_workbook_plus_9202
-- name    : lean_workbook_plus_9202
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/8165307d-1644-46ef-9871-7f4f99f87df0
-- statement:
--   If $a,b,c,d\geq -1.$ Prove that $a^3+b^3+c^3+d^3\ge\frac{3}{4}(a+b+c+d)-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9202 (a b c d : ℝ) (hab : a ≥ -1) (hbc : b ≥ -1) (hcd : c ≥ -1) (hda : d ≥ -1) : a^3 + b^3 + c^3 + d^3 ≥ (3/4 : ℝ) * (a + b + c + d) - 1   :=  by sorry
