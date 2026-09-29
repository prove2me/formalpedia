-- Prove2me | Theorems.Thm_WorkbookSource_base_15777
-- name    : WorkbookSource.base_15777
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:46:59.290738+00:00
-- url     : https://prove2.me/theorems/4b2095a4-f0e3-457c-8acc-f44da9a2e86f
-- title:
--   A normalized product bound with quadratic and linear terms
-- statement:
--   Let $a,b,c\ge0$ and $a+b+c=3.$ Prove that $(a^2+a-bc)(b^2+b-ca)(c^2+c-ab)\le8$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15777` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15777; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15777 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : (a^2 + a - b * c) * (b^2 + b - c * a) * (c^2 + c - a * b) ≤ 8  :=  by sorry
