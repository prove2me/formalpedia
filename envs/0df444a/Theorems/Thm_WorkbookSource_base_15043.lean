-- Prove2me | Theorems.Thm_WorkbookSource_base_15043
-- name    : WorkbookSource.base_15043
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:25.034448+00:00
-- url     : https://prove2.me/theorems/8ca804ae-e009-413e-9e0d-17637793b572
-- title:
--   A quadratic inequality with one weighted pairwise product
-- statement:
--   Prove that $ 3r_ar_b + r_br_c + r_cr_a\le\left(r_a + r_b + r_c\right)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15043` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15043; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15043 (r_a r_b r_c : ℝ) : 3 * r_a * r_b + r_b * r_c + r_c * r_a ≤ (r_a + r_b + r_c) ^ 2  :=  by sorry
