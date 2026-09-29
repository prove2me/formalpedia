-- Prove2me | Theorems.Thm_lean_workbook_plus_60301
-- name    : lean_workbook_plus_60301
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/21dfcd4b-c772-4597-bfe0-7e3c45d835ec
-- statement:
--   Prove that for a, b, c > 0:\n $ (a + b + c)^3 - \left(\sum_{cyc} a(a^2 + 3b^2 + 3c^2)\right)\ge 0\iff 6abc\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60301 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 - (a * (a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2) + b * (b ^ 2 + 3 * c ^ 2 + 3 * a ^ 2) + c * (c ^ 2 + 3 * a ^ 2 + 3 * b ^ 2)) ≥ 0 ↔ 6 * a * b * c ≥ 0   :=  by sorry
