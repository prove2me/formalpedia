-- Prove2me | Theorems.Thm_lean_workbook_plus_6773
-- name    : lean_workbook_plus_6773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/6ed19cd3-c386-48e9-8351-637693215e99
-- statement:
--   For $a,b>0$ , prove the following inequality: $8(a^2+2)^2(b^2+2)^2\ge 81(a+b)^2+36ab(a^2+2)(b^2+2)$ Also prove the equality holds if and only if $a=b=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6773 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 8 * (a^2 + 2)^2 * (b^2 + 2)^2 ≥ 81 * (a + b)^2 + 36 * a * b * (a^2 + 2) * (b^2 + 2)   :=  by sorry
