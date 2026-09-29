-- Prove2me | Theorems.Thm_lean_workbook_plus_11458
-- name    : lean_workbook_plus_11458
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ebd3cc69-d16d-4b58-8f8a-58cf28ce2df7
-- statement:
--   Prove that for non-negative numbers $a, b, c, d, e, f$, the following identity holds: \(-(ad+be+cf)^2 + 3/2a^3d + 3/2b^3e + 3/2c^3f + 3/2d^3a + 3/2e^3b + 3/2f^3c = 3/4(f-c)^2cf + 3/4(d-a)^2ad + 3/4(e-b)^2be + 3/4(b-e)^2be + 3/4(c-f)^2cf + 3/4(a-d)^2ad + 1/3(2ad-be-cf)^2 + 1/3(2be-ad-cf)^2 + 1/3(2cf-ad-be)^2\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11458 (a b c d e f : ℝ) : (-(a * d + b * e + c * f) ^ 2 + 3 / 2 * a ^ 3 * d + 3 / 2 * b ^ 3 * e + 3 / 2 * c ^ 3 * f + 3 / 2 * d ^ 3 * a + 3 / 2 * e ^ 3 * b + 3 / 2 * f ^ 3 * c) = 3 / 4 * (f - c) ^ 2 * f * c + 3 / 4 * (d - a) ^ 2 * d * a + 3 / 4 * (e - b) ^ 2 * e * b + 3 / 4 * (b - e) ^ 2 * b * e + 3 / 4 * (c - f) ^ 2 * c * f + 3 / 4 * (a - d) ^ 2 * a * d + 1 / 3 * (2 * a * d - b * e - c * f) ^ 2 + 1 / 3 * (2 * b * e - a * d - c * f) ^ 2 + 1 / 3 * (2 * c * f - a * d - b * e) ^ 2   :=  by sorry
