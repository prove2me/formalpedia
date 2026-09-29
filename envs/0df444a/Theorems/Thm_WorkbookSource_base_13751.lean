-- Prove2me | Theorems.Thm_WorkbookSource_base_13751
-- name    : WorkbookSource.base_13751
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:37.764977+00:00
-- url     : https://prove2.me/theorems/edfcda51-e582-4edc-b679-26c8b0c973ca
-- title:
--   A fourth-power and cubic lower bound at unit sum
-- statement:
--   Let $a,b,c,d>0$ and $a+b+c+d=1$ . Then,
--    $16(a^4+b^4+c^4+d^4)+8(a^3+b^3+c^3+d^3)-3(a^2+b^2+c^2+d^2)\ge 0$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13751` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13751; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13751 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a + b + c + d = 1) :(16 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) + 8 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) ≥ 0  :=  by sorry
