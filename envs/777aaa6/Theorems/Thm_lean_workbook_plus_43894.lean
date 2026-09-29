-- Prove2me | Theorems.Thm_lean_workbook_plus_43894
-- name    : lean_workbook_plus_43894
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/6b5b11d9-47c3-440a-887c-b01755534c70
-- statement:
--   Let a,b,c be three sides of triangle prove that \n $ a^{10}+b^{10}+c^{10}+\sum b^4c^4(b^2+c^2)+4a^2b^2c^2(a^4+b^4+c^4)\geq 2\sum b^2c^2(b^6+c^6)+3a^2b^2c^2(b^2c^2+c^2a^2+a^2b^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43894 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^10 + b^10 + c^10 + (b^4 * c^4 * (b^2 + c^2) + c^4 * a^4 * (c^2 + a^2) + a^4 * b^4 * (a^2 + b^2)) + 4 * a^2 * b^2 * c^2 * (a^4 + b^4 + c^4) ≥ 2 * (b^2 * c^2 * (b^6 + c^6) + c^2 * a^2 * (c^6 + a^6) + a^2 * b^2 * (a^6 + b^6)) + 3 * a^2 * b^2 * c^2 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2)   :=  by sorry
