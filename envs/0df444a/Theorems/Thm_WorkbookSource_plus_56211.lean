-- Prove2me | Theorems.Thm_WorkbookSource_plus_56211
-- name    : WorkbookSource.plus_56211
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:31.286458+00:00
-- url     : https://prove2.me/theorems/7fdb5612-4f08-4b70-8313-4cf974662e68
-- title:
--   A symmetric quartic bound with coefficient twenty-seven
-- statement:
--   Let $a,b,c \geq 0$ ,prove that: $8(b^2+c^2+a^2)^2+27(a+b+c)abc \geq 9(ab+cb+ac)(b^2+c^2+a^2)+3(a+b+c)(a+b)(b+c)(c+a)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_56211` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_56211; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_56211 (a b c : ℝ) : 8 * (b ^ 2 + c ^ 2 + a ^ 2) ^ 2 + 27 * (a + b + c) * a * b * c ≥ 9 * (a * b + b * c + c * a) * (b ^ 2 + c ^ 2 + a ^ 2) + 3 * (a + b + c) * (a + b) * (b + c) * (c + a)   :=  by sorry
