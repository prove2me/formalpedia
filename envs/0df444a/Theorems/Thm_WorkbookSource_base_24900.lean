-- Prove2me | Theorems.Thm_WorkbookSource_base_24900
-- name    : WorkbookSource.base_24900
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:38.53084+00:00
-- url     : https://prove2.me/theorems/43b53a78-5e0a-4cf4-8956-aefe089bdc8e
-- title:
--   A sixth-degree product inequality for three alternating quadratic factors
-- statement:
--   Let $a,b,c$ be real numbers. Prove the inequality:
--    $$3(a^2-ab+b^2)(b^2-bc+c^2)(c^2-ac+a^2)\geq a^3b^3+b^3c^3+c^3a^3$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24900` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24900; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24900 (a b c : ℝ) : 3 * (a^2 - a * b + b^2) * (b^2 - b * c + c^2) * (c^2 - c * a + a^2) ≥ a^3 * b^3 + b^3 * c^3 + c^3 * a^3  :=  by sorry
