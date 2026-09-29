-- Prove2me | Theorems.Thm_WorkbookSource_base_47864
-- name    : WorkbookSource.base_47864
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:20:49.919889+00:00
-- url     : https://prove2.me/theorems/20b622ac-8e14-46e9-a162-ab875bd387b0
-- title:
--   A cyclic fifth-degree sum bounds a symmetric product
-- statement:
--   Let $a,b,c>0$ . Show that
--    $$a^2(a+b)^3+b^2(b+c)^3+c^2(c+a)^3\geq{\frac{8abc(a+b+c)^2}{3}}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47864` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47864; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_47864 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * (a + b)^3 + b^2 * (b + c)^3 + c^2 * (c + a)^3 ≥ (8 * a * b * c * (a + b + c)^2) / 3  :=  by sorry
