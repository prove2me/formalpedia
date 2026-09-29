-- Prove2me | Theorems.Thm_lean_workbook_plus_16379
-- name    : lean_workbook_plus_16379
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e0c01e05-a4f2-485d-b6b3-09229bb46451
-- statement:
--   $=(b-c)^2(a-c)^2+(c-a)^2(b-a)^2+(a-b)^2(c-b)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16379 (a b c : ℝ) : (b - c) ^ 2 * (a - c) ^ 2 + (c - a) ^ 2 * (b - a) ^ 2 + (a - b) ^ 2 * (c - b) ^ 2 = (b ^ 2 - 2 * b * c + c ^ 2) * (a ^ 2 - 2 * a * c + c ^ 2) + (c ^ 2 - 2 * c * a + a ^ 2) * (b ^ 2 - 2 * b * a + a ^ 2) + (a ^ 2 - 2 * a * b + b ^ 2) * (c ^ 2 - 2 * c * b + b ^ 2)   :=  by sorry
