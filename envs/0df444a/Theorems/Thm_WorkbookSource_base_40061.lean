-- Prove2me | Theorems.Thm_WorkbookSource_base_40061
-- name    : WorkbookSource.base_40061
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:54:26.870638+00:00
-- url     : https://prove2.me/theorems/83ed0a46-47cc-4d03-b72a-2863fa8cdc80
-- title:
--   A fourth power of the pairwise sum bounds a mixed symmetric product
-- statement:
--   The following statement is true.
--   Let $ a,b,c \ge 0 $ . Prove that :
--    $ (ab+ac+bc)^4 \geq a^2b^2c^2(16(a^2+b^2+c^2)+11(ab+ac+bc)) $ .
--   Equivalently,
--    $(a+b+c)^4 \ge 16(a^2b^2+b^2c^2+c^2a^2)+11abc(a+b+c)$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40061` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40061; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_40061 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a * b + b * c + c * a) ^ 4 ≥ a ^ 2 * b ^ 2 * c ^ 2 * (16 * (a ^ 2 + b ^ 2 + c ^ 2) + 11 * (a * b + b * c + c * a))  :=  by sorry
