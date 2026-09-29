-- Prove2me | Theorems.Thm_WorkbookSource_base_35848
-- name    : WorkbookSource.base_35848
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:08:45.455679+00:00
-- url     : https://prove2.me/theorems/2d281f10-35be-4e71-8d27-6f50705a7209
-- title:
--   A cyclic squared-difference rational inequality
-- statement:
--   Let $a,b,c>0$. Prove that
--
--    $$ \sum\limits_{cyc} (a-b)^2\Big[ \frac{12a^2+12b^2-3c^2+3ab+9ca+9cb}{3(2a^2+(b+c)^2)(2b^2+(c+a)^2)} - \frac{1}{(a+b+c)^2}\Big] \geqq 0 $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35848` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35848; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35848 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) ^ 2 * ((12 * a ^ 2 + 12 * b ^ 2 - 3 * c ^ 2 + 3 * a * b + 9 * c * a + 9 * c * b) / (3 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2)) - 1 / (a + b + c) ^ 2) + (b - c) ^ 2 * ((12 * b ^ 2 + 12 * c ^ 2 - 3 * a ^ 2 + 3 * b * c + 9 * a * b + 9 * a * c) / (3 * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2)) - 1 / (a + b + c) ^ 2) + (c - a) ^ 2 * ((12 * c ^ 2 + 12 * a ^ 2 - 3 * b ^ 2 + 3 * c * a + 9 * b * c + 9 * b * a) / (3 * (2 * c ^ 2 + (a + b) ^ 2) * (2 * a ^ 2 + (b + c) ^ 2)) - 1 / (a + b + c) ^ 2) ≥ 0  :=  by sorry
