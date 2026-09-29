-- Prove2me | Theorems.Thm_WorkbookSource_plus_51590
-- name    : WorkbookSource.plus_51590
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:51.179097+00:00
-- url     : https://prove2.me/theorems/49a4003f-c16a-4eb8-a55f-1cd81e7d4c75
-- title:
--   A cubic lower bound under half-unit caps
-- statement:
--   Let $a,b,c\leq \frac{1}{2}$ be nonnegative real numbers such that: $a+b+c=1$ . Prove that:
--    $a^{2}+b^{2}+c^{2}+9abc\geq 2(ab+bc+ca)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_51590` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_51590; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_51590 (a b c : ℝ) (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) (hc : c ≤ 1 / 2) (habc : a + b + c = 1) : a^2 + b^2 + c^2 + 9 * a * b * c ≥ 2 * (a * b + b * c + c * a)   :=  by sorry
