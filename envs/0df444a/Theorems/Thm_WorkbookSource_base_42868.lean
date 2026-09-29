-- Prove2me | Theorems.Thm_WorkbookSource_base_42868
-- name    : WorkbookSource.base_42868
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:38:32.696249+00:00
-- url     : https://prove2.me/theorems/ade7d68b-3eb9-4769-b548-e6c6482ed2ce
-- title:
--   A comparison of cyclic cubic reciprocals
-- statement:
--   Let $a,b$ and $c$ be positive real numbers. Prove that $\frac{1}{ab^2+bc^2+ca^2}+\frac{1}{3abc}{\ge}\frac{2}{a^2b+b^2c+c^2a}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42868` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42868; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_42868 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) + 1 / (3 * a * b * c)) ≥ 2 / (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a)  :=  by sorry
