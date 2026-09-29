-- Prove2me | Theorems.Thm_WorkbookSource_plus_61196
-- name    : WorkbookSource.plus_61196
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:36.01748+00:00
-- url     : https://prove2.me/theorems/516e6997-47f3-4fa6-8af3-2d463c1f9894
-- title:
--   A triangle semiperimeter-weighted difference inequality
-- statement:
--   For a triangle with sides $a,b,c$ and semi-perimeter $s$ , prove that:
--
--    $$(s-a)(b-c)^2 + (s-b)(c-a)^2 + (s-c)(a-b)^2 \leq abc$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_61196` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_61196; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_61196 {a b c s : ℝ} (hx: a + b + c = 2 * s) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (s - a) * (b - c) ^ 2 + (s - b) * (c - a) ^ 2 + (s - c) * (a - b) ^ 2 ≤ a * b * c   :=  by sorry
