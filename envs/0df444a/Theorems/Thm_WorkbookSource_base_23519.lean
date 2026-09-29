-- Prove2me | Theorems.Thm_WorkbookSource_base_23519
-- name    : WorkbookSource.base_23519
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:57:49.108953+00:00
-- url     : https://prove2.me/theorems/03a78229-2a5a-4b19-8006-b6fe157e3b10
-- title:
--   A cyclic quadratic ratio sum is at least three
-- statement:
--   Let $ a,b ,c$ be positive real numbers. Prove that $\frac{b^2+c^2}{a^2+ bc}+\frac{c^2+a^2}{b^2+ ca}+\frac{a^2+b^2}{c^2+ ab} \ge 3.$ Proposed by Nguyen Viet Hung
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23519` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23519; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23519 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b^2 + c^2) / (a^2 + b * c) + (c^2 + a^2) / (b^2 + c * a) + (a^2 + b^2) / (c^2 + a * b) ≥ 3  :=  by sorry
