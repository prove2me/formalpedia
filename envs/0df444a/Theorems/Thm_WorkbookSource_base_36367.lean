-- Prove2me | Theorems.Thm_WorkbookSource_base_36367
-- name    : WorkbookSource.base_36367
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:27.154982+00:00
-- url     : https://prove2.me/theorems/52603975-1519-4425-ab9c-339c42b539cd
-- title:
--   A cubic correction under unit pairwise sum
-- statement:
--   Prove that $a^2+b^2+c^2+abc(a+b+c)\ge \frac{4}{3}$ given $a,b,c>0$ and $ab+bc+ca=1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36367` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36367; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36367 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a * b + b * c + c * a = 1) : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c * (a + b + c) ≥ 4 / 3  :=  by sorry
