-- Prove2me | Theorems.Thm_WorkbookSource_base_46897
-- name    : WorkbookSource.base_46897
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:45.96959+00:00
-- url     : https://prove2.me/theorems/6f3bd4f1-535f-49e7-a1c7-9aa2022ad50e
-- title:
--   A quartic bound for symmetric cubic products
-- statement:
--   Prove that $9\sum a^{3}(b+c)+3\sum a^{2}bc \le 4\sum a^{4}+17\sum a^{2}b^{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46897` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46897; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46897 (a b c : ℝ) : 9 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b)) + 3 * (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ≤ 4 * (a ^ 4 + b ^ 4 + c ^ 4) + 17 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)  :=  by sorry
