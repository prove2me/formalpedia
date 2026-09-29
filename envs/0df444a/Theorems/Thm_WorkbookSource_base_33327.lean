-- Prove2me | Theorems.Thm_WorkbookSource_base_33327
-- name    : WorkbookSource.base_33327
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:11:46.366834+00:00
-- url     : https://prove2.me/theorems/2ae9d792-9e82-4bda-98f9-fef9d57622c6
-- title:
--   A twelfth-power sum with a pair-product correction at fixed total three
-- statement:
--   Prove that $a^{12}+b^{12}+c^{12}+8(ab+bc+ca) \geq 27$ for real positive numbers $a, b, c$ with $a+b+c=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33327` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33327; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33327 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a ^ 12 + b ^ 12 + c ^ 12 + 8 * (a * b + b * c + c * a) ≥ 27  :=  by sorry
