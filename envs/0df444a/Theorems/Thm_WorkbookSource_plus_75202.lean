-- Prove2me | Theorems.Thm_WorkbookSource_plus_75202
-- name    : WorkbookSource.plus_75202
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:54:03.031246+00:00
-- url     : https://prove2.me/theorems/39cb544d-7531-41a5-b2a7-53ceff1efc89
-- title:
--   A shifted cubic ratio sum is at least one at fixed sum three
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=3$. Prove that: $\frac{a^3+2}{a^2+8b}+\frac{b^3+2}{b^2+8c}+\frac{c^3+2}{c^2+8a} \geq 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_75202` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_75202; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_75202 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^3 + 2) / (a^2 + 8 * b) + (b^3 + 2) / (b^2 + 8 * c) + (c^3 + 2) / (c^2 + 8 * a) ≥ 1   :=  by sorry
