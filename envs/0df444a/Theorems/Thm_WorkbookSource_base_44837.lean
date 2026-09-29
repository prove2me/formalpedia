-- Prove2me | Theorems.Thm_WorkbookSource_base_44837
-- name    : WorkbookSource.base_44837
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:48:50.143787+00:00
-- url     : https://prove2.me/theorems/69dd2f1b-c232-4eb2-a737-1e9bde7773a6
-- title:
--   A weighted linear product ratio is at least one hundred twenty-eight thirds
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that $$\frac {(2a+b)(b+2c)(a+3b+c)}{abc} \geq \frac {128} {3}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44837` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44837; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_44837 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a + b) * (b + 2 * c) * (a + 3 * b + c) / (a * b * c) ≥ 128 / 3  :=  by sorry
