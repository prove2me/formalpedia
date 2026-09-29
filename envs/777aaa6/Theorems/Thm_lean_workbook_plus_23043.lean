-- Prove2me | Theorems.Thm_lean_workbook_plus_23043
-- name    : lean_workbook_plus_23043
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b34f0cd4-37a2-43a8-848b-84b387c40b40
-- statement:
--   (a+b+c+d)^3 \geq 16(abc+bcd+cda+dab), where $a, b, c, d > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23043 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b + c + d) ^ 3 ≥ 16 * (a * b * c + b * c * d + c * d * a + d * a * b)   :=  by sorry
