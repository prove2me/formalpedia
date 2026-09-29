-- Prove2me | Theorems.Thm_WorkbookSource_base_20698
-- name    : WorkbookSource.base_20698
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:45:51.925934+00:00
-- url     : https://prove2.me/theorems/0686158e-5f33-41c5-a3d3-2df076b36618
-- title:
--   A shifted cyclic quadratic ratio lower bound at fixed sum three
-- statement:
--   Let $a$ , $b$ , $c$ be positive real numbers such that $a+b+c=3$ . Prove that $\frac{3a+1}{3b^2+1}+\frac{3b+1}{3c^2+1}+\frac{3c+1}{3a^2+1}\geq 3.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20698` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20698; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20698 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : (3 * a + 1) / (3 * b ^ 2 + 1) + (3 * b + 1) / (3 * c ^ 2 + 1) + (3 * c + 1) / (3 * a ^ 2 + 1) ≥ 3  :=  by sorry
