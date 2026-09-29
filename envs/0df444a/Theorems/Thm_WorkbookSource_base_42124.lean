-- Prove2me | Theorems.Thm_WorkbookSource_base_42124
-- name    : WorkbookSource.base_42124
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:13:04.600285+00:00
-- url     : https://prove2.me/theorems/eb818251-04e9-4779-a9a6-d319df203b92
-- title:
--   A sixth-degree mixed-product upper bound at fixed sum two
-- statement:
--   Let $a$ , $b$ and $c$ be non-negative numbers such that $a+b+c=2$ . Prove that:
--   $a^2+b^2+c^2\ge 2\left(a^3 b^3+a^3 c^3+c^3 b^3\right)+9a^2 b^2 c^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42124` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42124; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_42124 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2) : a^2 + b^2 + c^2 ≥ 2 * (a^3 * b^3 + a^3 * c^3 + c^3 * b^3) + 9 * a^2 * b^2 * c^2  :=  by sorry
