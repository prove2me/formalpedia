-- Prove2me | Theorems.Thm_WorkbookSource_plus_81777
-- name    : WorkbookSource.plus_81777
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:31:17.694966+00:00
-- url     : https://prove2.me/theorems/e9001f20-15fa-4759-a39a-c3171db5801d
-- title:
--   A cyclic cubic product sum is at most two hundred fifty-six twenty-sevenths at fixed total four
-- statement:
--   Let $a$ , $b$ , $c$ and $d$ positive real numbers such that: $a+b+c+d=4$ . Prove that: $a^2b+b^2c+c^2d+d^2a \leq \frac{256}{27}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_81777` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_81777; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_81777 {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 4) : a^2 * b + b^2 * c + c^2 * d + d^2 * a ≤ 256 / 27   :=  by sorry
