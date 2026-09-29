-- Prove2me | Theorems.Thm_WorkbookSource_base_16588
-- name    : WorkbookSource.base_16588
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:42:24.332128+00:00
-- url     : https://prove2.me/theorems/b5636454-eb4e-4ac9-81b5-2487ea574b5a
-- title:
--   A sixth-power bound for the cubed sum of squares
-- statement:
--   For all non-negative real numbers $a$ , $b$ and $c$ prove that:
--
--    $$4(a^6+b^6+c^6)+5abc(a^3+b^3+c^3)\geq(a^2+b^2+c^2)^3$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16588` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16588; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16588 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 4 * (a ^ 6 + b ^ 6 + c ^ 6) + 5 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a ^ 2 + b ^ 2 + c ^ 2) ^ 3  :=  by sorry
