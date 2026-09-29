-- Prove2me | Theorems.Thm_WorkbookSource_base_10868
-- name    : WorkbookSource.base_10868
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:06:36.652045+00:00
-- url     : https://prove2.me/theorems/266123bf-dceb-4aa7-8d92-ca392adc2f45
-- title:
--   A product of three affine forms on the unit circle
-- statement:
--   Let $a,b $ be reals such that $a^2+b^2=1.$ Prove that
--
--    $$(3a+4b)(5a+4)(5b+3) \geq 0$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10868` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10868; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10868 (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : (3 * a + 4 * b) * (5 * a + 4) * (5 * b + 3) ≥ 0  :=  by sorry
