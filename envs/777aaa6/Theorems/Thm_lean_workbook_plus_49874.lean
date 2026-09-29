-- Prove2me | Theorems.Thm_lean_workbook_plus_49874
-- name    : lean_workbook_plus_49874
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c2302c0f-efc7-42e7-8f24-e3f2abc1aab3
-- statement:
--   $(a^2 +1)(b^2 +1) \geq \frac{3}{4} ((a+b)^2 +(ab)^2)$ iff $(a-b)^2 + (ab-2)^2 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49874 : (a^2 + 1) * (b^2 + 1) ≥ (3 / 4) * ((a + b)^2 + (a * b)^2) ↔ (a - b)^2 + (a * b - 2)^2 ≥ 0   :=  by sorry
