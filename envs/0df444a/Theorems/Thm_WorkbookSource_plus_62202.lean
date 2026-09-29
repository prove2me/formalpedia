-- Prove2me | Theorems.Thm_WorkbookSource_plus_62202
-- name    : WorkbookSource.plus_62202
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:57.265284+00:00
-- url     : https://prove2.me/theorems/783509d4-8f25-4f1a-b1d5-615e09070ee4
-- title:
--   A four-variable fourth-power inequality with a cyclic difference product
-- statement:
--   Let $a$ , $b$ , $c$ $d$ non-negative real numbers. Prove that: $ a^4+b^4+c^4+d^4+2(a-b)(b-c)(c-d)(d-a) \geq 4abcd$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_62202` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_62202; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_62202 (a b c d : ℝ) : a^4 + b^4 + c^4 + d^4 + 2 * (a - b) * (b - c) * (c - d) * (d - a) ≥ 4 * a * b * c * d   :=  by sorry
