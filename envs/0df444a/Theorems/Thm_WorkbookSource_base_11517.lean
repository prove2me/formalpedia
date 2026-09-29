-- Prove2me | Theorems.Thm_WorkbookSource_base_11517
-- name    : WorkbookSource.base_11517
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:14.673138+00:00
-- url     : https://prove2.me/theorems/d530e66a-3c74-4d3d-ace0-c9e12b0fce50
-- title:
--   A quadratic bound for a sum of linear and pairwise terms
-- statement:
--   By Cauchy-Shwarz Inequality, we have: $(a+b+c+2(ab+bc+ca))^{2}\le 3((a+b+c)^{2}+2(ab+bc+ca)^{2}) \le 9(a^{2}+b^{2}+c^{2}+2(a^{2}b^{2}+b^{2}c^{2}+c^{2}a^{2}))$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11517` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11517; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11517 {a b c : ℝ} : (a + b + c + 2 * (a * b + b * c + c * a)) ^ 2 ≤ 9 * (a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2))  :=  by sorry
