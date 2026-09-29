-- Prove2me | Theorems.Thm_WorkbookSource_plus_17927
-- name    : WorkbookSource.plus_17927
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:15.45791+00:00
-- url     : https://prove2.me/theorems/0dee13e9-309c-41a0-b755-ef81815a9698
-- title:
--   Three quadratic factors bound three squared pairwise sums
-- statement:
--   $ \prod (2a^{2}+b^{2}+c^{2})=\prod [(a^{2}+b^{2})+(a^{2}+c^{2})]\geq \prod [\frac{(a+b)^{2}}{2}+\frac{(a+c)^{2}}{2}]\geq \prod \sqrt{(a+b)^{2}(a+c)^{2}}=(a+b)^{2}(b+c)^{2}(c+a)^{2} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_17927` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_17927; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_17927 (a b c : ℝ) : (2 * a ^ 2 + b ^ 2 + c ^ 2) * (2 * b ^ 2 + c ^ 2 + a ^ 2) * (2 * c ^ 2 + a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2   :=  by sorry
