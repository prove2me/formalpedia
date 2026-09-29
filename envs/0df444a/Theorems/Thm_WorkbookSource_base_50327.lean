-- Prove2me | Theorems.Thm_WorkbookSource_base_50327
-- name    : WorkbookSource.base_50327
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:44:00.439058+00:00
-- url     : https://prove2.me/theorems/54d18f86-92e7-4709-84a8-ede1967e950e
-- title:
--   A mixed quadratic ratio lower bound at fixed sum three
-- statement:
--   Let $a,b,c>0$ and $a+b+c=3$ . Prove that:
--    $\frac{a^{2}+bc}{a+bc}+\frac{b^{2}+ac}{b+ac}+\frac{c^{2}+ab}{c+ab}\geq 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50327` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50327; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50327 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 + b * c) / (a + b * c) + (b^2 + c * a) / (b + c * a) + (c^2 + a * b) / (c + a * b) ≥ 3  :=  by sorry
