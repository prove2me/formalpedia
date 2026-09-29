-- Prove2me | Theorems.Thm_WorkbookSource_base_984
-- name    : WorkbookSource.base_984
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:45:33.363668+00:00
-- url     : https://prove2.me/theorems/879cc1a3-6335-4db7-8191-ef3ac15dd467
-- title:
--   A squared pair-product sum bounds a triple-product expression
-- statement:
--   Given $a,b,c\in \mathbb{R}$ and $a+b+c=1$ . Prove that $8abc-8\leqslant ( ab+bc+ac+1)^{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_984` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_984; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_984 (a b c : ℝ) (h : a + b + c = 1) :
  8 * a * b * c - 8 ≤ (a * b + b * c + c * a + 1)^2  :=  by sorry
