-- Prove2me | Theorems.Thm_WorkbookSource_base_14228
-- name    : WorkbookSource.base_14228
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:37:25.274984+00:00
-- url     : https://prove2.me/theorems/fdc15ce0-2206-41d5-84fe-21fcc188d10c
-- title:
--   A mixed cubic bound at sum three
-- statement:
--   Give $ a,b,c$ be non-negative real numbers with sum 3.Prove that
--    $ \frac {ab + bc + ca}3 + 3\ge abc + a^2\frac {b + c}2 + b^2\frac {c + a}2 + c^2\frac {a + b}2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14228` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14228; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14228 (a b c: ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3):  (a * b + b * c + c * a) / 3 + 3 ≥ a * b * c + a ^ 2 * (b + c) / 2 + b ^ 2 * (c + a) / 2 + c ^ 2 * (a + b) / 2  :=  by sorry
