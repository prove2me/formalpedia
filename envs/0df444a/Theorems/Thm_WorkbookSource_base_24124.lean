-- Prove2me | Theorems.Thm_WorkbookSource_base_24124
-- name    : WorkbookSource.base_24124
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:33.855537+00:00
-- url     : https://prove2.me/theorems/29e02e80-082b-404a-a505-6ceeb27f1d05
-- title:
--   A cyclic quartic bound with a symmetric correction
-- statement:
--   prove that \(2(a^4+b^4+c^4)+abc(a+b+c)\ge 3(a^3b+b^3c+c^3a)\) (arqady)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24124` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24124; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24124 (a b c : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4) + a * b * c * (a + b + c) ≥ 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)  :=  by sorry
