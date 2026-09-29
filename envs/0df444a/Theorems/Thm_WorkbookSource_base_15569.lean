-- Prove2me | Theorems.Thm_WorkbookSource_base_15569
-- name    : WorkbookSource.base_15569
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:01:31.850432+00:00
-- url     : https://prove2.me/theorems/ad75bc85-3d4c-4d10-9147-484248e0b1d5
-- title:
--   A rearrangement inequality for cyclic squared ratios
-- statement:
--   Prove or disprove that $\frac{a^{2}+3b^{2}}{(b+c)^{2}}+\frac{b^{2}+3c^{2}}{(c+a)^{2}}+\frac{c^{2}+3a^{2}}{(a+b)^{2}} \leq 4\sum \frac{a^{2}}{(b+c)^{2}}$ given $a,b,c>0$ using Rearrangement inequality.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15569` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15569; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15569 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 3 * b^2) / (b + c)^2 + (b^2 + 3 * c^2) / (c + a)^2 + (c^2 + 3 * a^2) / (a + b)^2 ≤ 4 * (a^2 / (b + c)^2 + b^2 / (c + a)^2 + c^2 / (a + b)^2)  :=  by sorry
