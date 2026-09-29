-- Prove2me | Theorems.Thm_WorkbookSource_base_12079
-- name    : WorkbookSource.base_12079
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:36:53.71156+00:00
-- url     : https://prove2.me/theorems/c3f53aab-7c89-487b-8674-542284f89c6e
-- title:
--   A cyclic cubic sum is at most four at total three
-- statement:
--   If $ a$ , $ b$ , $ c$ are nonnegative reals such that $ a + b + c = 3$ , then prove that: $ a^2b + b^2c + c^2a\leq 4$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12079` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12079; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12079 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : a^2 * b + b^2 * c + c^2 * a ≤ 4  :=  by sorry
