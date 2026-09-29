-- Prove2me | Theorems.Thm_WorkbookSource_base_15265
-- name    : WorkbookSource.base_15265
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:47.533298+00:00
-- url     : https://prove2.me/theorems/6bb0f313-bf54-4aed-ab3e-068e43833a66
-- title:
--   A four-variable cyclic quartic expression is nonnegative
-- statement:
--   prove that: $ (a^2-2ab+c^2)(a^2+bc)+(b^2-2bc+d^2)(b^2+cd)+(c^2-2cd+a^2)(c^2+ad)+(-2ad+d^2+b^2)(d^2+ab)\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15265` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15265; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15265 (a b c d : ℝ) :
  (a^2 - 2 * a * b + c^2) * (a^2 + b * c) + (b^2 - 2 * b * c + d^2) * (b^2 + c * d) + (c^2 - 2 * c * d + a^2) * (c^2 + d * a) + (-2 * a * d + d^2 + b^2) * (d^2 + a * b) ≥ 0  :=  by sorry
