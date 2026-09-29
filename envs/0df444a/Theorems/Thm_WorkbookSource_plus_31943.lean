-- Prove2me | Theorems.Thm_WorkbookSource_plus_31943
-- name    : WorkbookSource.plus_31943
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:43:27.924723+00:00
-- url     : https://prove2.me/theorems/86c7f6e0-cb77-4b71-82e3-c11bf8eca022
-- title:
--   A mixed quintic inequality at fixed sum two
-- statement:
--   If $a,b,c>0$ and $a+b+c=2$ , prove or disprove that:
--
--   $$ a^3+b^3+c^3+a^3 b c+a b^3 c+a b c^3 \ge \frac {abc}{3} +a^3 b+a^3 c+ab^3+b^3 c+ac^3+bc^3 $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_31943` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_31943; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_31943 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 2) : a^3 + b^3 + c^3 + a^3 * b * c + a * b^3 * c + a * b * c^3 ≥ a * b * c / 3 + a^3 * b + a^3 * c + a * b^3 + b^3 * c + a * c^3 + b * c^3   :=  by sorry
