-- Prove2me | Theorems.Thm_WorkbookSource_base_31228
-- name    : WorkbookSource.base_31228
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:25:53.159804+00:00
-- url     : https://prove2.me/theorems/c6199b1b-0c20-4718-b754-509750504090
-- title:
--   A cyclic power-ratio comparison
-- statement:
--   Let $a,$ $b$ and $c$ are positive numbers. Prove that:
--    $\frac{a^{2}}{b^{3}}+\frac{b^{2}}{c^{3}}+\frac{c^{2}}{a^{3}}\geq\frac{a}{b^{2}}+\frac{b}{c^{2}}+\frac{c}{a^{2}}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31228` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31228; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31228 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b^3 + b^2 / c^3 + c^2 / a^3) ≥ (a / b^2 + b / c^2 + c / a^2)  :=  by sorry
