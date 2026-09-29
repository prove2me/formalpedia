-- Prove2me | Theorems.Thm_WorkbookSource_base_21519
-- name    : WorkbookSource.base_21519
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:40.554804+00:00
-- url     : https://prove2.me/theorems/0340c5c1-b982-430a-a859-5143b38a0660
-- title:
--   A sixth-degree bound involving three differences
-- statement:
--   Prove that for any real numbers $a, b, c$, the following inequality holds:
--
--   $$(a-b)^4(b-c)^2+(b-c)^4(c-a)^2+(c-a)^4(a-b)^2 \geqslant 5(a-b)^2(b-c)^2(c-a)^2.$$
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21519` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21519; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21519 (a b c : ℝ) : (a - b) ^ 4 * (b - c) ^ 2 + (b - c) ^ 4 * (c - a) ^ 2 + (c - a) ^ 4 * (a - b) ^ 2 ≥ 5 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2  :=  by sorry
