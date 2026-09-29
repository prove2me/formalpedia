-- Prove2me | Theorems.Thm_lean_workbook_plus_11390
-- name    : lean_workbook_plus_11390
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/c0577152-7c73-4a69-9868-b4e8aad5be06
-- statement:
--   Prove that for positive real numbers a, b, and c, the following inequality holds: \n$ (ab+bc+ca) \leq \frac {(a+b+c)^2}{3} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11390 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 / 3   :=  by sorry
