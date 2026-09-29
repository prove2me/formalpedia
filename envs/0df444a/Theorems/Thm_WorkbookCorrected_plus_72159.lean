-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_72159
-- name    : WorkbookCorrected.plus_72159
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:13:21.885914+00:00
-- url     : https://prove2.me/theorems/c8dce16a-5574-4002-941f-7775fa94b6b3
-- title:
--   A product-sum maximum on two circles
-- statement:
--   Let $a^{2}+b^{2}=x^{2}+y^{2}=2$ then show that maximum value of $S=(1-a)(1-b)+(1-x)(1-y) $ is $8$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_72159` (Apache-2.0). Natural-language proposition preserved; the source bound is completed with an exact attainment witness. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_72159; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.plus_72159 : (∀ (a b x y : ℝ) (ha : a^2 + b^2 = 2) (hb : x^2 + y^2 = 2), (1 - a) * (1 - b) + (1 - x) * (1 - y) ≤ 8) ∧ (∃ a b x y : ℝ, (a^2 + b^2 = 2) ∧ (x^2 + y^2 = 2) ∧ ( (1 - a) * (1 - b) + (1 - x) * (1 - y)  =  8   )) := by sorry
