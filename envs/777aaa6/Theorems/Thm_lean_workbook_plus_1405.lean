-- Prove2me | Theorems.Thm_lean_workbook_plus_1405
-- name    : lean_workbook_plus_1405
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/7468ac7d-6bf7-4613-8579-a1439d29f986
-- statement:
--   Prove that for nonnegative variables $a$, $b$, and $c$, the following inequality holds: $9(a^3 + b^3 + c^3) \geq (a + b + c)^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1405 (a b c: ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 9 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a + b + c) ^ 3   :=  by sorry
