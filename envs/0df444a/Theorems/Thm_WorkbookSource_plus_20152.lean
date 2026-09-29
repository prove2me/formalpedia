-- Prove2me | Theorems.Thm_WorkbookSource_plus_20152
-- name    : WorkbookSource.plus_20152
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:07:46.222072+00:00
-- url     : https://prove2.me/theorems/08ebf122-8a94-4090-9706-56b0336415c0
-- title:
--   An asymmetric quartic inequality involving a pairwise sum
-- statement:
--   Let $ a,b,c \geq 0$ ,prove that:
--
--    $ab(a+b)^2+2c^4 \geq 2abc(b+c+a).$
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_20152` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_20152; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_20152 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a * b * (a + b) ^ 2 + 2 * c ^ 4 ≥ 2 * a * b * c * (b + c + a)   :=  by sorry
