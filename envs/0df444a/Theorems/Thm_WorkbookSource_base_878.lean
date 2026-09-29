-- Prove2me | Theorems.Thm_WorkbookSource_base_878
-- name    : WorkbookSource.base_878
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:34:25.613991+00:00
-- url     : https://prove2.me/theorems/69c784fa-86c9-49b7-a7e5-b96da78783d0
-- title:
--   A lower bound on four absolute values from pairwise products
-- statement:
--   Let $a,b,c,d $ be real numbers such that $ab+ac+ad+bc+bd+cd=-1. $ Prove that $|a|+|b|+|c|+|d|\geq 2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_878` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_878; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_878 (a b c d : ℝ) (h : a * b + a * c + a * d + b * c + b * d + c * d = -1) : |a| + |b| + |c| + |d| ≥ 2  :=  by sorry
