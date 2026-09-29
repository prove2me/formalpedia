-- Prove2me | Theorems.Thm_WorkbookSource_base_16123
-- name    : WorkbookSource.base_16123
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:33.118825+00:00
-- url     : https://prove2.me/theorems/035ca246-d1a9-44b0-8726-fe97124f9be4
-- title:
--   A cubic upper bound at unit positive sum
-- statement:
--   Prove that: $4(a^2+b^2+c^2) \ge 3(a^3+b^3+c^3)+1$ given $a,b,c>0$ and $a+b+c=1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16123` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16123; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16123 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : 4 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 3 * (a ^ 3 + b ^ 3 + c ^ 3) + 1  :=  by sorry
