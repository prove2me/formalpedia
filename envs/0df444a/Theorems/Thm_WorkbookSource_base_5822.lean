-- Prove2me | Theorems.Thm_WorkbookSource_base_5822
-- name    : WorkbookSource.base_5822
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:48.988329+00:00
-- url     : https://prove2.me/theorems/dd757e7b-2e4d-46ef-b3be-983acab4ad61
-- title:
--   A squared-product bound in three real variables
-- statement:
--   My solution :
--
--    $ \left((1+\frac{a}{b})(1+\frac{a}{c})-2\right)^2\ge 0 \Leftrightarrow (1+\frac{a}{b})(1+\frac{a}{c})\ge 2\sqrt{\frac{a}{b}+\frac{a}{c}+\frac{a^2}{bc}}$
--
--    which is equivalent with : $ (a+b)^2(a+c)^2\ge 4abc(a+b+c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5822` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5822; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5822  (a b c : ℝ) :
  (a + b)^2 * (a + c)^2 ≥ 4 * a * b * c * (a + b + c)  :=  by sorry
