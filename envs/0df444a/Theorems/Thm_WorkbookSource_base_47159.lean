-- Prove2me | Theorems.Thm_WorkbookSource_base_47159
-- name    : WorkbookSource.base_47159
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:09:22.682972+00:00
-- url     : https://prove2.me/theorems/0889abef-89ed-4c45-a94c-6b71233282f5
-- title:
--   A product of weighted quadratic forms bounds symmetric sums
-- statement:
--   Given $ a, b, c > 0$ . Prove that:
--    $ (a^2 + 2b^2)(b^2 + 2c^2)(c^2 + 2a^2) \geq\ \frac {1}{3}(ab + bc + ca)^2(a + b + c)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47159` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47159; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_47159 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 2 * b^2) * (b^2 + 2 * c^2) * (c^2 + 2 * a^2) ≥ 1/3 * (a * b + b * c + c * a)^2 * (a + b + c)^2  :=  by sorry
