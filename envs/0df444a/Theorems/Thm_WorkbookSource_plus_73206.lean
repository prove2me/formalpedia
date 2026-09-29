-- Prove2me | Theorems.Thm_WorkbookSource_plus_73206
-- name    : WorkbookSource.plus_73206
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:33.278775+00:00
-- url     : https://prove2.me/theorems/772e130a-cd70-4a70-8e19-3c3cfb902815
-- title:
--   A cyclic quartic bound involving two symmetric corrections
-- statement:
--   Prove that $(a^{2}+b^{2}+c^{2})^{2}+3(a^{2}b^{2}+b^{2}c^{2}+c^{2}a^{2})\geq 3(ab^{3}+bc^{3}+ca^{3})+3abc(a+b+c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_73206` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_73206; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_73206 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 3 * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) + 3 * a * b * c * (a + b + c)   :=  by sorry
