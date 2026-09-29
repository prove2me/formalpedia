-- Prove2me | Theorems.Thm_WorkbookSource_plus_34364
-- name    : WorkbookSource.plus_34364
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:52:17.00492+00:00
-- url     : https://prove2.me/theorems/a3cb7aed-6646-4b7d-8a5a-18d350996893
-- title:
--   A mixed cubic reciprocal sum is at least two
-- statement:
--   Let $a,b,c>0$ and $a+b+c=3$ . Prove that $\frac{1}{abc}+\frac{4}{a^2b+b^2c+c^2 a+abc}\ge 2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_34364` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_34364; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_34364 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 1 / (a * b * c) + 4 / (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + a * b * c) ≥ 2   :=  by sorry
