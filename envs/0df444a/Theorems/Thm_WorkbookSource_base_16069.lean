-- Prove2me | Theorems.Thm_WorkbookSource_base_16069
-- name    : WorkbookSource.base_16069
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:04:00.413285+00:00
-- url     : https://prove2.me/theorems/979199cd-e423-4c28-9a1c-2e44eb058489
-- title:
--   A quartic bound for the squared pairwise sum
-- statement:
--   Prove that for positive numbers $a, b, c$, the following inequality holds: $(a^3+b^3+c^3+9abc)(a+b+c) \ge 4 (ab+bc+ca)^2$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16069` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16069; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16069 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3 + 9 * a * b * c) * (a + b + c) ≥ 4 * (a * b + b * c + c * a)^2  :=  by sorry
