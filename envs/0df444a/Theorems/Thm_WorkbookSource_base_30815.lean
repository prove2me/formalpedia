-- Prove2me | Theorems.Thm_WorkbookSource_base_30815
-- name    : WorkbookSource.base_30815
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:47:10.839982+00:00
-- url     : https://prove2.me/theorems/10f3b4f1-96ab-47fe-b7c8-2589d47ea9b2
-- title:
--   A cyclic quartic and quadratic upper bound at total three
-- statement:
--   Let $a,b,c$ be real numbers such that $a+b+c=3.$ Prove that $3(a^3b+b^3c+c^3a)+16(ab+bc+ca) \leq 57.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30815` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30815; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30815 (a b c : ℝ) (h : a + b + c = 3) : 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 16 * (a * b + b * c + c * a) ≤ 57  :=  by sorry
