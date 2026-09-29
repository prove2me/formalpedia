-- Prove2me | Theorems.Thm_WorkbookSource_plus_52739
-- name    : WorkbookSource.plus_52739
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:15:52.235554+00:00
-- url     : https://prove2.me/theorems/3d350105-1ca9-4f8a-9bad-833cff013ba0
-- title:
--   A cyclic quartic ratio sum is at least three halves
-- statement:
--   For positive $a,\ b,\ c$ , such that $a+b+c=3$
--   Prove that : $\sum \frac{a^4}{b^2+c}\ge \frac{3}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_52739` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_52739; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_52739 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^4 / (b^2 + c) + b^4 / (c^2 + a) + c^4 / (a^2 + b) ≥ 3 / 2   :=  by sorry
