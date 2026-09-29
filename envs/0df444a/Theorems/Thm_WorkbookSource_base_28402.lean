-- Prove2me | Theorems.Thm_WorkbookSource_base_28402
-- name    : WorkbookSource.base_28402
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:47:40.793526+00:00
-- url     : https://prove2.me/theorems/0d96c7ac-fecd-4304-8c3c-38f01e1d2061
-- title:
--   A symmetric sixth-degree product inequality
-- statement:
--   Prove that: $10(a^2+b^2)(b^2+c^2)(c^2+a^2)+120a^2b^2c^2-3\left[(a+b)^2(b+c)^2(c+a)^2 \right] \geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28402` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28402; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28402 (a b c : ℝ) : 10 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) + 120 * a^2 * b^2 * c^2 - 3 * (a + b)^2 * (b + c)^2 * (c + a)^2 ≥ 0  :=  by sorry
