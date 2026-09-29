-- Prove2me | Theorems.Thm_WorkbookSource_base_1776
-- name    : WorkbookSource.base_1776
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:10:58.868583+00:00
-- url     : https://prove2.me/theorems/46143b5b-9cba-455b-87e0-4203f52d95e4
-- title:
--   A distance bound between constrained pairs
-- statement:
--   Let $a, b, c, d$ be real numbers such that $a^2+b^2 =\frac{1}{2}$ and $cd = 1$ . Prove that $$(a - d)^2 + (b - c)^2\geq \frac{1}{2}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1776` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1776; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1776 (a b c d : ℝ) (h1 : a^2 + b^2 = 1/2) (h2 : c * d = 1) : (a - d)^2 + (b - c)^2 ≥ 1/2  :=  by sorry
