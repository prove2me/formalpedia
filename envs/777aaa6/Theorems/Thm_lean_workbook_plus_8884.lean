-- Prove2me | Theorems.Thm_lean_workbook_plus_8884
-- name    : lean_workbook_plus_8884
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/78367c43-3b33-47ca-ae50-105647f67b0a
-- statement:
--   Prove that for non-negative numbers $a, b, c, d, e$, the following identity holds: \((ab+bc+cd+de+ea)(ac+bd+ec+ad+be) - 5deca - 5deab - 5cbde - 5ebca - 5abcd = ce(a-b)^2 + de(a-c)^2 + bc(a-d)^2 + bd(a-e)^2 + ad(b-c)^2 + ae(b-d)^2 + cd(b-e)^2 + be(c-d)^2 + ab(c-e)^2 + ac(d-e)^2\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8884 (a b c d e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : (a * b + b * c + c * d + d * e + e * a) * (a * c + b * d + e * c + a * d + b * e) - 5 * d * e * c * a - 5 * d * e * a * b - 5 * c * b * d * e - 5 * e * b * c * a - 5 * a * b * c * d = c * e * (a - b) ^ 2 + d * e * (a - c) ^ 2 + b * c * (a - d) ^ 2 + b * d * (a - e) ^ 2 + a * d * (b - c) ^ 2 + a * e * (b - d) ^ 2 + c * d * (b - e) ^ 2 + b * e * (c - d) ^ 2 + a * b * (c - e) ^ 2 + a * c * (d - e) ^ 2   :=  by sorry
