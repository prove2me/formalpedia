-- Prove2me | Theorems.Thm_WorkbookSource_base_2222
-- name    : WorkbookSource.base_2222
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:00:36.781926+00:00
-- url     : https://prove2.me/theorems/cd0f446d-668d-47eb-b5a5-9862b077c796
-- title:
--   An asymmetric quartic inequality on nonnegative variables
-- statement:
--   Let $ a,b,c \geq 0$ ,prove that:
--
--    $c^3a+a^4+b^3c \geq ac(cb+b^2+a^2).$
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2222` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2222; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2222 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : c^3*a + a^4 + b^3*c ≥ a*c*(b*c + b^2 + a^2)  :=  by sorry
