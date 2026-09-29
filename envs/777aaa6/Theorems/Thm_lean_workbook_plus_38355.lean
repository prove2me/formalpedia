-- Prove2me | Theorems.Thm_lean_workbook_plus_38355
-- name    : lean_workbook_plus_38355
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9a7535d9-dbc5-4359-bc58-417eb10b10a5
-- statement:
--   Let $a,b,c \geq 0$ ,prove that: $2c^5+a^3(b+c)^2 \geq 2ac(c^3+abc+a^2b).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38355 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 2 * c ^ 5 + a ^ 3 * (b + c) ^ 2 ≥ 2 * a * c * (c ^ 3 + a * b * c + a ^ 2 * b)   :=  by sorry
