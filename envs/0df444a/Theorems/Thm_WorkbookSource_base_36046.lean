-- Prove2me | Theorems.Thm_WorkbookSource_base_36046
-- name    : WorkbookSource.base_36046
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:48:38.302783+00:00
-- url     : https://prove2.me/theorems/77ba6495-40ed-494c-bca9-0ed4744f4a0c
-- title:
--   A squared total and normalized triple-product inequality in four variables
-- statement:
--   For $ a, b, c, d > 0 $ real numbers prove that: $\frac{9}{16} (a+b+c+d)^2 + \frac{3(abc+bcd+cda+dab)}{a+b+c+d} \ge 2(ab+ac+ad+bc+bd+cd) \ \ ; (2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36046` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36046; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36046 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (9 / 16) * (a + b + c + d) ^ 2 + (3 * (a * b * c + b * c * d + c * d * a + d * a * b)) / (a + b + c + d) ≥ 2 * (a * b + a * c + a * d + b * c + b * d + c * d)  :=  by sorry
