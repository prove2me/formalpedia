-- Prove2me | Theorems.Thm_lean_workbook_plus_37301
-- name    : lean_workbook_plus_37301
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/2ec8f8e3-65a4-4b0f-abbd-fffabe7257ea
-- statement:
--   Prove that for positive real numbers a, b, and c, the following identity holds:\n$$2(a^2+b^2)(b^2+c^2)(c^2+a^2)-(a^2b+b^2c+c^2a+a^2c+c^2b+b^2a-2abc)^2=(a-b)^2(b-c)^2(c-a)^2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37301 :  ∀ a b c : ℝ, 2 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) - (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + a ^ 2 * c + c ^ 2 * b + b ^ 2 * a - 2 * a * b * c) ^ 2 = (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2   :=  by sorry
