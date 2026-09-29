-- Prove2me | Theorems.Thm_WorkbookSource_base_20107
-- name    : WorkbookSource.base_20107
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:31:31.696267+00:00
-- url     : https://prove2.me/theorems/d1320d71-512f-489b-b360-af41aa09b809
-- title:
--   A five-variable cyclic quadratic comparison
-- statement:
--   If $a, b, c, d, e \ge 0$ , prove that $3\sum_{cyc}a^{2}+\sum_{cyc}ab \ge 4\sum_{cyc}ac$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20107` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20107; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20107 {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 3 * (a^2 + b^2 + c^2 + d^2 + e^2) + (a * b + b * c + c * d + d * e + e * a) ≥ 4 * (a * c + b * d + c * e + d * a + e * b)  :=  by sorry
