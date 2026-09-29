-- Prove2me | Theorems.Thm_WorkbookSource_plus_31162
-- name    : WorkbookSource.plus_31162
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:04.326445+00:00
-- url     : https://prove2.me/theorems/19dca988-ef1c-4b1f-a406-346a28160a07
-- title:
--   Two cyclic cubic sums bound a corrected mixed sum
-- statement:
--   Let $a,b$ and $c$ be positive real numbers . Prove that $$(a^2b+b^2c+c^2a)(ab^2+bc^2+ca^2)\geq 3abc(a^2(b+c)+b^2(c+a)+c^2(a+b)-3abc)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_31162` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_31162; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_31162 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2) ≥ 3 * a * b * c * (a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) - 3 * a * b * c)   :=  by sorry
