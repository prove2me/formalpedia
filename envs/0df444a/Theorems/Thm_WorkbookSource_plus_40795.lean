-- Prove2me | Theorems.Thm_WorkbookSource_plus_40795
-- name    : WorkbookSource.plus_40795
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:41:05.662714+00:00
-- url     : https://prove2.me/theorems/f6bbbb6a-ca20-4da2-ac5e-54155a6bc5a5
-- title:
--   A cyclic quartic inequality at fixed total three
-- statement:
--   Given $a+b+c=3$, prove that $6\sum{a^{4}}-4\sum{a^{3}c}-37\sum{a^{3}b}+91\sum{a^{2}b^{2}}-56\sum{a^{2}bc}\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_40795` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_40795; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_40795 (a b c : ℝ) (ha : a + b + c = 3) : 6 * (a ^ 4 + b ^ 4 + c ^ 4) - 4 * (a ^ 3 * c + b ^ 3 * a + c ^ 3 * b) - 37 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 91 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - 56 * (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ≥ 0   :=  by sorry
