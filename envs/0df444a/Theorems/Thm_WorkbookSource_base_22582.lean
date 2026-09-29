-- Prove2me | Theorems.Thm_WorkbookSource_base_22582
-- name    : WorkbookSource.base_22582
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:40:28.46002+00:00
-- url     : https://prove2.me/theorems/70271bee-d4c4-4d2c-b584-a3cda2f0caaa
-- title:
--   A shifted quadratic ratio with a product reciprocal lower bound
-- statement:
--   Let $a,b>0$. Prove that
--
--    $$ \frac{ a^2+ b^2+1}{(a+1)(b+1)}+\frac{2ab}{ ab( ab+3)} \geq \frac{5}{4} $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22582` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22582; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_22582 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^2 + b^2 + 1) / (a + 1) / (b + 1) + 2 * a * b / (a * b * (a * b + 3)) ≥ 5 / 4  :=  by sorry
