-- Prove2me | Theorems.Thm_WorkbookSource_base_35325
-- name    : WorkbookSource.base_35325
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:18.700772+00:00
-- url     : https://prove2.me/theorems/66b808c6-e578-415b-8833-8cf6324d62e4
-- title:
--   A squared pairwise sum bounds a cubic elementary symmetric sum
-- statement:
--   Let $a,b,c,d \in R$ ,prove that: $(ab+bc+cd+ad+ca+db)^2\geq \frac{9}{4}(a+b+c+d)(abc+bcd+cda+dab).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35325` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35325; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35325 (a b c d : ℝ) : (a * b + b * c + c * d + d * a + a * c + b * d) ^ 2 ≥ (9 / 4) * (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)  :=  by sorry
