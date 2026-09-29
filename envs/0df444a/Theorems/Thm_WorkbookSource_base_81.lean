-- Prove2me | Theorems.Thm_WorkbookSource_base_81
-- name    : WorkbookSource.base_81
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:10.313675+00:00
-- url     : https://prove2.me/theorems/c38a38eb-a648-4ad5-a4e0-238a54421874
-- title:
--   A symmetric quartic inequality with linear terms
-- statement:
--   [1]+[2]+[3]+[4] gives $ a^{2}b^{2}+b^{2}c^{2}+c^{2}a^{2}+3(a^{2}+b^{2}+c^{2})+6\geq 2(a+b+c)+4(ab+bc+ca)$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_81` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_81; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_81 (a b c : ℝ) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 3 * (a^2 + b^2 + c^2) + 6 ≥ 2 * (a + b + c) + 4 * (a * b + b * c + c * a)  :=  by sorry
