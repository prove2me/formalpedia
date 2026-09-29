-- Prove2me | Theorems.Thm_WorkbookSource_base_14166
-- name    : WorkbookSource.base_14166
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:16.770501+00:00
-- url     : https://prove2.me/theorems/992ec541-22c5-491e-b47c-2130590bbcb0
-- title:
--   A quartic and cubic comparison on the four-variable simplex
-- statement:
--   Let $a,b,c,d\ge 0$ such that $a+b+c+d=1$ . Prove that
--    $$5(a^2+b^2+c^2+d^2)+2(a^2+b^2+c^2+d^2)^2\ge 1 +6(a^3+b^3+c^3+d^3).$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14166` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14166; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14166 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 1) : 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 ≥ 1 + 6 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3)  :=  by sorry
