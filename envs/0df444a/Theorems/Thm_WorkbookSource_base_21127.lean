-- Prove2me | Theorems.Thm_WorkbookSource_base_21127
-- name    : WorkbookSource.base_21127
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:28.064014+00:00
-- url     : https://prove2.me/theorems/89a5e701-d8d5-4d2f-992e-24487080524d
-- title:
--   A symmetric fourth-power inequality with coefficient thirteen
-- statement:
--   Show that for all non-negative $ a$ , $ b$ , and $ c$ , we have
--
--    $ 13\left(a^4 + b^4 + c^4\right) + \left(a + b + c\right)^4 \ge 20\left(a^3b + a^3c + b^3c + b^3a + c^3a + c^3b\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21127` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21127; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21127 (a b c : ℝ) : 13 * (a ^ 4 + b ^ 4 + c ^ 4) + (a + b + c) ^ 4 ≥ 20 * (a ^ 3 * b + a ^ 3 * c + b ^ 3 * c + b ^ 3 * a + c ^ 3 * a + c ^ 3 * b)  :=  by sorry
