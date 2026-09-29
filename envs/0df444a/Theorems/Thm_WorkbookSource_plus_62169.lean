-- Prove2me | Theorems.Thm_WorkbookSource_plus_62169
-- name    : WorkbookSource.plus_62169
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:11:53.299104+00:00
-- url     : https://prove2.me/theorems/77e687ea-c3df-481c-b443-86525d68dbe3
-- title:
--   An inequality with powers two, four and eight
-- statement:
--   Let $a$ , $b$ , $c$ and $d$ be real positive numbers. Prove that: $4a^2 + 2b^4 + c^8 + d^8 \geq 8abcd$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_62169` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_62169; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.plus_62169 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 4 * a ^ 2 + 2 * b ^ 4 + c ^ 8 + d ^ 8 ≥ 8 * a * b * c * d   :=  by sorry
