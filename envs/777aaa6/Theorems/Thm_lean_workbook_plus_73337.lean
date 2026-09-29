-- Prove2me | Theorems.Thm_lean_workbook_plus_73337
-- name    : lean_workbook_plus_73337
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e4651d5d-fe8b-4ffd-812c-92970504dedf
-- statement:
--   Prove that for non-negative reals a, b, and c, the inequality \(2(a^3 + b^3 + c^3) \geq a^2(b+c) + b^2(a+c) + c^2(a+b)\) holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73337 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 2 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b)   :=  by sorry
