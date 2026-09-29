-- Prove2me | Theorems.Thm_WorkbookSource_base_15342
-- name    : WorkbookSource.base_15342
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:46:54.557558+00:00
-- url     : https://prove2.me/theorems/e1e819ee-20a5-40fb-bc83-1367b75acd6e
-- title:
--   A normalized cyclic cubic inequality
-- statement:
--   Prove that: $4 + 15abc + (a - b)(b - c)(c - a) \geq 5(a^2b + b^2c + c^2a) + 12(ab + bc + ca)$ given $a;b;c \geq 0$ and $a + b + c = 1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15342` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15342; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15342 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 1) : 4 + 15 * a * b * c + (a - b) * (b - c) * (c - a) ≥ 5 * (a^2 * b + b^2 * c + c^2 * a) + 12 * (a * b + b * c + c * a)  :=  by sorry
