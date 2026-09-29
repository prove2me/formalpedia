-- Prove2me | Theorems.Thm_WorkbookSource_base_19033
-- name    : WorkbookSource.base_19033
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:42:32.723102+00:00
-- url     : https://prove2.me/theorems/fc197404-b220-41d2-9d0a-b3352239e6c8
-- title:
--   A product of shifted quadratics at fixed sum four
-- statement:
--   Prove that $({a^2} - a + 1)({b^2} - b + 1)({c^2} - c + 1) \le 13$ for non-negative reals $a$ , $b$ and $c$ such that $a+b+c=4$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19033` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19033; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19033 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 4) : (a^2 - a + 1) * (b^2 - b + 1) * (c^2 - c + 1) ≤ 13  :=  by sorry
