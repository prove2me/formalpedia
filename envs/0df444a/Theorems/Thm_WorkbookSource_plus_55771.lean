-- Prove2me | Theorems.Thm_WorkbookSource_plus_55771
-- name    : WorkbookSource.plus_55771
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:40:46.421413+00:00
-- url     : https://prove2.me/theorems/ea44951f-b261-4f48-924a-b196ea29fdfa
-- title:
--   A shifted cyclic reciprocal sum is at least one
-- statement:
--   For positive reals $a, b, c$ such that $a + b + c = 3$. Prove that: $\\sum_{cyc}{\\frac {a}{b^2 + 2}}\\ge 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_55771` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_55771; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_55771 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (b ^ 2 + 2) + b / (c ^ 2 + 2) + c / (a ^ 2 + 2) ≥ 1   :=  by sorry
