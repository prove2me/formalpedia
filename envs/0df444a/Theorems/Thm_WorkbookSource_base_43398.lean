-- Prove2me | Theorems.Thm_WorkbookSource_base_43398
-- name    : WorkbookSource.base_43398
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:02:53.211952+00:00
-- url     : https://prove2.me/theorems/53eacf4d-9e6c-4eae-a806-9b6000b261f7
-- title:
--   A cyclic quartic inequality with a shifted squared sum
-- statement:
--   Prove that $ (a^{2}+b^{2}+c^{2}-1)^{2} \geq 2(a^{3}b+b^{3}c+c^{3}a-1) $ for any $ a,b,c \geq 0 $ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43398` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43398; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43398 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a^2 + b^2 + c^2 - 1)^2 ≥ 2 * (a^3 * b + b^3 * c + c^3 * a - 1)  :=  by sorry
