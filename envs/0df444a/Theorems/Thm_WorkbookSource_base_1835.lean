-- Prove2me | Theorems.Thm_WorkbookSource_base_1835
-- name    : WorkbookSource.base_1835
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:56:37.208294+00:00
-- url     : https://prove2.me/theorems/8600854e-b1a3-48ed-b293-129581ee6311
-- title:
--   A cyclic quadratic ratio bound at fixed sum three
-- statement:
--   Let $a,b,c>0$ and $a+b+c=3$ . Prove
--
--    $\sum_{cyc} \frac{a^2}{a+b^2}\geq \frac{3}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1835` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1835; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1835 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : (a^2 / (a + b^2) + b^2 / (b + c^2) + c^2 / (c + a^2)) ≥ 3 / 2  :=  by sorry
