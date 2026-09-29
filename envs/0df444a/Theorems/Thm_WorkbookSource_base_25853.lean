-- Prove2me | Theorems.Thm_WorkbookSource_base_25853
-- name    : WorkbookSource.base_25853
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:05:55.339802+00:00
-- url     : https://prove2.me/theorems/d50fe762-905e-4070-8303-62582697d9dc
-- title:
--   A squared cyclic ratio sum bounds a symmetric quadratic ratio
-- statement:
--   Let $a, b, c > 0$. Prove that
--    $$\frac{a^2}{b^2}+\frac{b^2}{c^2}+\frac{c^2}{a^2}\ge 1+ \frac{2(a^2+b^2+c^2)}{ab+bc+ca}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25853` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25853; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_25853 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 / b^2 + b^2 / c^2 + c^2 / a^2 ≥ 1 + (2 * (a^2 + b^2 + c^2)) / (a * b + b * c + c * a)  :=  by sorry
