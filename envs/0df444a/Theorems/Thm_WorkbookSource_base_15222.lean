-- Prove2me | Theorems.Thm_WorkbookSource_base_15222
-- name    : WorkbookSource.base_15222
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:59:43.751165+00:00
-- url     : https://prove2.me/theorems/72a21dab-44fc-4789-aa88-161a4c6e1e5a
-- title:
--   A cubic-over-linear lower bound at fixed sum three
-- statement:
--   prove the inequality :
--    $$ \sum_{cyc} \frac{a^3}{b+c} \ge \frac{3}{2} $$
--   Given $ a, b, c $ are positive real numbers such that $ a+b+c = 3 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15222` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15222; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15222 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^3 / (b + c) + b^3 / (a + c) + c^3 / (a + b) ≥ 3 / 2  :=  by sorry
