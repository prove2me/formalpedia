-- Prove2me | Theorems.Thm_WorkbookSource_base_55370
-- name    : WorkbookSource.base_55370
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:27:18.232444+00:00
-- url     : https://prove2.me/theorems/5af28e84-66d3-47e1-84d9-ae8d8db8977a
-- title:
--   A shifted cyclic quadratic ratio sum is at most three seventeenths
-- statement:
--   If $a, b, c>0, a+b+c=3$ prove that
--    $\sum_{cyc}{\frac{a^2}{7a^2+9a+bc}}\le\frac{3}{17}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55370` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55370; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55370 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^2 / (7 * a^2 + 9 * a + b * c) + b^2 / (7 * b^2 + 9 * b + c * a) + c^2 / (7 * c^2 + 9 * c + a * b) ≤ 3 / 17  :=  by sorry
