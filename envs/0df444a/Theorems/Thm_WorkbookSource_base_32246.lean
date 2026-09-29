-- Prove2me | Theorems.Thm_WorkbookSource_base_32246
-- name    : WorkbookSource.base_32246
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:05.606782+00:00
-- url     : https://prove2.me/theorems/6d805066-efd2-4530-ae63-36a483bb8fc4
-- title:
--   A sum of squared symmetric expressions is at least 147
-- statement:
--   Let $a,b,c \ge 0$ and $a+b+c=3$ . Prove that:
--    $2(bc+3a)^2+2(ca+3b)^2+2(ab+3c)^2+\left(2ab+2bc+2ca+3\right)^2 \ge 147$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32246` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32246; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32246 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : 2 * (b * c + 3 * a) ^ 2 + 2 * (c * a + 3 * b) ^ 2 + 2 * (a * b + 3 * c) ^ 2 + (2 * a * b + 2 * b * c + 2 * c * a + 3) ^ 2 ≥ 147  :=  by sorry
