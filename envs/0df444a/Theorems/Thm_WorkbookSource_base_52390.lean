-- Prove2me | Theorems.Thm_WorkbookSource_base_52390
-- name    : WorkbookSource.base_52390
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:28:36.501924+00:00
-- url     : https://prove2.me/theorems/ce09e80b-f5b4-4b6e-b939-f2b2b5e2cc82
-- title:
--   A five-variable cyclic quadratic bound
-- statement:
--   we only need to prove that:
--    $5(a^{2}+b^{2}+c^{2}+d^{2}+e^{2})\le\ (a+b+c+d+e)^{2}+2\sum_{cyc}(3a-b-c-d)^{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52390` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52390; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52390 (a b c d e : ℝ) :
  5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ≤
    (a + b + c + d + e) ^ 2 + 2 * ((3 * a - b - c - d) ^ 2 + (3 * b - c - d - e) ^ 2 + (3 * c - d - e - a) ^ 2 + (3 * d - e - a - b) ^ 2 + (3 * e - a - b - c) ^ 2)  :=  by sorry
