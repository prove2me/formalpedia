-- Prove2me | Theorems.Thm_WorkbookSource_base_37186
-- name    : WorkbookSource.base_37186
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:53.773698+00:00
-- url     : https://prove2.me/theorems/7bf1608c-126f-4877-b420-368e1a237893
-- title:
--   A quartic norm bound with a cubic correction
-- statement:
--   For non-negative $a,b,c$ such that $a+b+c=3$ prove that $$(a^2+b^2+c^2)^2-2(a^3+b^3+c^3) \geq \frac{189}{64}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37186` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37186; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37186 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3) : (a^2 + b^2 + c^2)^2 - 2 * (a^3 + b^3 + c^3) ≥ 189 / 64  :=  by sorry
