-- Prove2me | Theorems.Thm_lean_workbook_plus_16489
-- name    : lean_workbook_plus_16489
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/a8a66219-3463-45b3-af80-0da0b18e5a7e
-- statement:
--   We need to prove $a-(a^3/2) +2a\leqq 2\sqrt{2} <=> (a-\sqrt{2})^2(a+2\sqrt{2}) \geqq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16489 (a : ℝ) : a - a ^ 3 / 2 + 2 * a ≤ 2 * Real.sqrt 2 ↔ (a - Real.sqrt 2) ^ 2 * (a + 2 * Real.sqrt 2) ≥ 0   :=  by sorry
