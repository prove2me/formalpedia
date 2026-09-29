-- Prove2me | Theorems.Thm_WorkbookSource_base_38516
-- name    : WorkbookSource.base_38516
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:53.478414+00:00
-- url     : https://prove2.me/theorems/02ad6456-8d14-48f9-9a81-3d017b655845
-- title:
--   A complementary product bound at unit sum
-- statement:
--   Prove $(1-a)(1-b)(1-c) \geq 8abc$ given $a+b+c=1$ and $a, b, c \in \mathbb{R}^{+}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38516` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38516; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38516 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : (1 - a) * (1 - b) * (1 - c) ≥ 8 * a * b * c  :=  by sorry
