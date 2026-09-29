-- Prove2me | Theorems.Thm_WorkbookSource_base_55115
-- name    : WorkbookSource.base_55115
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:23:01.552436+00:00
-- url     : https://prove2.me/theorems/1a295fc0-080e-49e9-8798-a858f626d6a0
-- title:
--   A shifted cyclic cubic ratio sum is at least six
-- statement:
--   Prove that for $a,b,c\in \mathbf{R^+}$ and $a+b+c=3$, the following inequality holds:
--   $\frac{a^3+5}{b+2}+\frac{b^3+5}{c+2}+\frac{c^3+5}{a+2}\geq 6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55115` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55115; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55115 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^3 + 5) / (b + 2) + (b^3 + 5) / (c + 2) + (c^3 + 5) / (a + 2) ≥ 6  :=  by sorry
