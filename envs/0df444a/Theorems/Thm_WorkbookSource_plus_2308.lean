-- Prove2me | Theorems.Thm_WorkbookSource_plus_2308
-- name    : WorkbookSource.plus_2308
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:55:55.616963+00:00
-- url     : https://prove2.me/theorems/c13eaaea-3591-44b1-816f-0396e54b98be
-- title:
--   A shifted cubic ratio sum is at least three halves
-- statement:
--   Let $a$ , $b$ and $c$ be positive real numbers such that $a+b+c=3$ . Prove the inequality
--
--    $$\frac{a^3}{a^2+1}+\frac{b^3}{b^2+1}+\frac{c^3}{c^2+1} \geq \frac{3}{2}.$$
--
--    Proposed by Anastasija Trajanova
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_2308` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_2308; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_2308 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^3 / (a^2 + 1) + b^3 / (b^2 + 1) + c^3 / (c^2 + 1) ≥ 3 / 2   :=  by sorry
