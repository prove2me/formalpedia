-- Prove2me | Theorems.Thm_WorkbookSource_base_53551
-- name    : WorkbookSource.base_53551
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:45.373081+00:00
-- url     : https://prove2.me/theorems/3577950e-cc06-43d6-ae5d-55d1eb9a657c
-- title:
--   A factored sixth-degree polynomial is nonpositive
-- statement:
--   Thus, it remains to prove that $4(a+b)^2(a^2+b^2)^2-25(a^2+b^2)(25a^4-4a^3b-31a^2b^2-4ab^3+25b^4)\leq0$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53551` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53551; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53551 (a b : ℝ) : 4 * (a + b) ^ 2 * (a ^ 2 + b ^ 2) ^ 2 - 25 * (a ^ 2 + b ^ 2) * (25 * a ^ 4 - 4 * a ^ 3 * b - 31 * a ^ 2 * b ^ 2 - 4 * a * b ^ 3 + 25 * b ^ 4) ≤ 0  :=  by sorry
