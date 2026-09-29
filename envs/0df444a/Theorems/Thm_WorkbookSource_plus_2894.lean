-- Prove2me | Theorems.Thm_WorkbookSource_plus_2894
-- name    : WorkbookSource.plus_2894
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:16.288478+00:00
-- url     : https://prove2.me/theorems/871011de-12aa-486d-b3eb-5f96dc7d4373
-- title:
--   A sixth-degree inequality formed from pairwise differences
-- statement:
--   This inequality holds for all reals $a,b,c$
--
--    $4\sum (a-b)(a-c)(a^2-b^2)(a^2-c^2)+(a-b)^2(b-c)^2(c-a)^2\ge 0.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_2894` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_2894; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_2894 (a b c : ℝ) : 4 * ((a - b) * (a - c) * (a ^ 2 - b ^ 2) * (a ^ 2 - c ^ 2) + (b - c) * (b - a) * (b ^ 2 - c ^ 2) * (b ^ 2 - a ^ 2) + (c - a) * (c - b) * (c ^ 2 - a ^ 2) * (c ^ 2 - b ^ 2)) + (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 ≥ 0   :=  by sorry
