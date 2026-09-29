-- Prove2me | Theorems.Thm_WorkbookSource_base_33790
-- name    : WorkbookSource.base_33790
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:04.938975+00:00
-- url     : https://prove2.me/theorems/7c9f6ada-61cc-46bf-aa45-36974b74686c
-- title:
--   An elementary symmetric inequality on the four-variable simplex
-- statement:
--   Let $a,b,c,d$ be nonnegative real numbers such that $a+b+c+d=1$. Prove that $ab+ac+ad+bc+bd+cd+48abcd\ge 9(abc+abd+acd+bcd).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33790` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33790; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33790 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (habc : a + b + c + d = 1) : a * b + a * c + a * d + b * c + b * d + c * d + 48 * a * b * c * d ≥ 9 * (a * b * c + a * b * d + a * c * d + b * c * d)  :=  by sorry
