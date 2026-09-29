-- Prove2me | Theorems.Thm_WorkbookSource_base_44682
-- name    : WorkbookSource.base_44682
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:49:35.665063+00:00
-- url     : https://prove2.me/theorems/e661f787-5ae9-49f6-9153-31d32ac79a48
-- title:
--   A four-variable squared-total inequality with a quartic ratio correction
-- statement:
--   Prove that for positive numbers $a, b, c, d$, the following inequality holds: $\frac{1}{4}(a+b+c+d)^2 \geq ac + bd + \frac{abc^2 + cbd^2 + a^2cd + b^2ad}{ac + bd}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44682` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44682; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_44682 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 / 4) * (a + b + c + d) ^ 2 ≥ a * c + b * d + (a * b * c ^ 2 + b * c * d ^ 2 + a ^ 2 * c * d + b ^ 2 * a * d) / (a * c + b * d)  :=  by sorry
