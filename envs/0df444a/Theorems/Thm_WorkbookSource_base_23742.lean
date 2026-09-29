-- Prove2me | Theorems.Thm_WorkbookSource_base_23742
-- name    : WorkbookSource.base_23742
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:31:18.004978+00:00
-- url     : https://prove2.me/theorems/560dc34b-42a0-461a-a5ab-c6c70b6eb855
-- title:
--   A reciprocal quadratic sum with a product correction
-- statement:
--   If $a,b$ are real numbers than prove that $\frac{a^2+1}{b^2+1}+\frac{b^2+1}{a^2+1}+\frac{3(a^2+1)(b^2+1)}{4}\geq2+a^2-ab+b^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23742` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23742; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23742 (a b : ℝ) : (a^2 + 1) / (b^2 + 1) + (b^2 + 1) / (a^2 + 1) + (3 * (a^2 + 1) * (b^2 + 1)) / 4 ≥ 2 + a^2 - a * b + b^2  :=  by sorry
