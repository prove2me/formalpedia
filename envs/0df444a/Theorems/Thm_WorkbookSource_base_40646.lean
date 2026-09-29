-- Prove2me | Theorems.Thm_WorkbookSource_base_40646
-- name    : WorkbookSource.base_40646
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:54:44.560891+00:00
-- url     : https://prove2.me/theorems/69f1ca51-dca4-4aae-bee2-f41588308348
-- title:
--   A shifted pairwise cubic ratio lower bound at fixed sum three
-- statement:
--   Prove that $\frac{a^3+b^3}{ab+1}+\frac{b^3+c^3}{bc+1}+\frac{c^3+a^3}{ca+1}\geq3$ given $a,b,c>0$ and $a+b+c=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40646` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40646; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_40646 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^3 + b^3) / (a * b + 1) + (b^3 + c^3) / (b * c + 1) + (c^3 + a^3) / (c * a + 1) ≥ 3  :=  by sorry
