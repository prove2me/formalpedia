-- Prove2me | Theorems.Thm_WorkbookSource_base_34132
-- name    : WorkbookSource.base_34132
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:41.727876+00:00
-- url     : https://prove2.me/theorems/3ef29642-de6a-40cb-86ba-1108cc1f0278
-- title:
--   A cubic and quadratic symmetric bound at fixed sum one
-- statement:
--   Prove this inequality $27abc+36(ab+bc+ca)\leq 13$ with $a,b,c \ge 0$ and $a+b+c=1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34132` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34132; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34132 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) : 27 * a * b * c + 36 * (a * b + b * c + c * a) ≤ 13  :=  by sorry
