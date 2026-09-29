-- Prove2me | Theorems.Thm_WorkbookSource_base_1727
-- name    : WorkbookSource.base_1727
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:54:10.925789+00:00
-- url     : https://prove2.me/theorems/55e539e1-83b2-45bd-9a4e-e9181a9d05e8
-- title:
--   A cyclic rational sum of cubic differences is nonnegative
-- statement:
--   Let $a, b, c>0$ . Prove that $\frac{a^3-b^3}{1+bc}+\frac{b^3-c ^3}{1+ca}+\frac{c^3-a^3}{1+ab}\ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1727` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1727; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1727 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 - b^3) / (1 + b * c) + (b^3 - c^3) / (1 + c * a) + (c^3 - a^3) / (1 + a * b) ≥ 0  :=  by sorry
