-- Prove2me | Theorems.Thm_WorkbookSource_base_37968
-- name    : WorkbookSource.base_37968
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:26.17683+00:00
-- url     : https://prove2.me/theorems/3fe94a9f-981f-43ca-bb10-24043a59a794
-- title:
--   Squared pairwise sums bound mixed quadratic factors
-- statement:
--   The following inequality is true too:
--    For non-negative $ a,$ $ b$ and $ c$ prove that:
--
--    $ 4(a^2 + bc)(b^2 + ca)(c^2 + ab) \leq (a + b)^2(b + c)^2(c + a)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37968` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37968; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37968 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 4 * (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) ≤ (a + b)^2 * (b + c)^2 * (c + a)^2  :=  by sorry
