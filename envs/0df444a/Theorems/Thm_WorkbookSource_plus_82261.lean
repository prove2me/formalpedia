-- Prove2me | Theorems.Thm_WorkbookSource_plus_82261
-- name    : WorkbookSource.plus_82261
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:12:12.075503+00:00
-- url     : https://prove2.me/theorems/18a995f3-3572-4113-8acd-990a8f3ae933
-- title:
--   A sharp bound with one linear variable
-- statement:
--   Let $a,b,c> 0$ and $a+b^2+c^2=4 .$ Prove that
--    $$a^2+b^2+c^2 \geq \frac{15}{4}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_82261` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_82261; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.plus_82261 (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0)(hab : a + b^2 + c^2 = 4) : a^2 + b^2 + c^2 ≥ 15 / 4   :=  by sorry
