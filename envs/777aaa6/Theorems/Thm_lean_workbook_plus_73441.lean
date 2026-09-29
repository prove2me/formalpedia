-- Prove2me | Theorems.Thm_lean_workbook_plus_73441
-- name    : lean_workbook_plus_73441
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/8af0a94f-56cb-4806-870c-82ff259fa692
-- statement:
--   prove $(b-c)^2a^2c^2((a^2-c^2)^2+2b^2(a+c-b)^2-b^4)+(b-c)^2b^2c^2((b^2-c^2)^2+2a^2(b+c-a)^2-a^4)\geq(b-c)^2c^2(a^2(a^2-c^2)^2+2a^2b^2(a+c-b)^2-a^2b^4+b^2(b^2-c^2)^2+2a^2b^2(b+c-a)^2-b^2a^4)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73441 (a b c : ℝ) : (b - c) ^ 2 * a ^ 2 * c ^ 2 * ((a ^ 2 - c ^ 2) ^ 2 + 2 * b ^ 2 * (a + c - b) ^ 2 - b ^ 4) + (b - c) ^ 2 * b ^ 2 * c ^ 2 * ((b ^ 2 - c ^ 2) ^ 2 + 2 * a ^ 2 * (b + c - a) ^ 2 - a ^ 4) ≥ (b - c) ^ 2 * c ^ 2 * (a ^ 2 * (a ^ 2 - c ^ 2) ^ 2 + 2 * a ^ 2 * b ^ 2 * (a + c - b) ^ 2 - a ^ 2 * b ^ 4 + b ^ 2 * (b ^ 2 - c ^ 2) ^ 2 + 2 * a ^ 2 * b ^ 2 * (b + c - a) ^ 2 - b ^ 2 * a ^ 4)   :=  by sorry
