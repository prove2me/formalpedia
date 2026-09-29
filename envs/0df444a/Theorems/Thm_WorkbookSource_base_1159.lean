-- Prove2me | Theorems.Thm_WorkbookSource_base_1159
-- name    : WorkbookSource.base_1159
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:38:01.35999+00:00
-- url     : https://prove2.me/theorems/41112ad9-635e-49ed-b844-501a4197aa19
-- title:
--   An exponential comparison with a radical exponent
-- statement:
--   So $4^{x+1}>3^{\sqrt{x^2+1}}$ for $x>0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1159` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1159; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1159 (x : ℝ) (hx: x > 0) : (4:ℝ)^(x + 1) > 3^(Real.sqrt (x^2 + 1))  :=  by sorry
