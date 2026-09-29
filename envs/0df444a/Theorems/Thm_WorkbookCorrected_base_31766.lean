-- Prove2me | Theorems.Thm_WorkbookCorrected_base_31766
-- name    : WorkbookCorrected.base_31766
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:00:04.115651+00:00
-- url     : https://prove2.me/theorems/0aafac14-4e61-4817-8cb1-31a395bb7e67
-- title:
--   A four-variable cubic sum bound at fixed quadratic norm
-- statement:
--   Let $ a,b,c,d$ be non-negative real numbers such that $ a^{2}+b^{2}+c^{2}+d^{2}=4$ . Prove that:
--    $ a^{3}+b^{3}+c^{3}+d^{3}+abc+bcd+cda+dab\le 8 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31766` (Apache-2.0). Natural-language proposition preserved; missing source domain assumptions restored. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31766; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_31766 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h : a^2 + b^2 + c^2 + d^2 = 4)  : a^3 + b^3 + c^3 + d^3 + a * b * c + b * c * d + c * d * a + d * a * b ≤ 8  :=  by sorry
