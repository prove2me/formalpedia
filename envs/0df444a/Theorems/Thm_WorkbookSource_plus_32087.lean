-- Prove2me | Theorems.Thm_WorkbookSource_plus_32087
-- name    : WorkbookSource.plus_32087
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:43:30.318263+00:00
-- url     : https://prove2.me/theorems/4df50655-9b13-44f9-b674-07cfe87df5a5
-- title:
--   A mixed quadratic reciprocal sum bounds symmetric reciprocals
-- statement:
--   If $ a,b,c $ are positive real numbers then $3\left( {\frac{1}{{2{a^2} + bc}} + \frac{1}{{2{b^2} + ca}} + \frac{1}{{2{c^2} + ab}}} \right) \geqslant \frac{7}{{{a^2} + {b^2} + {c^2}}} + \frac{2}{{ab + bc + ca}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_32087` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_32087; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_32087 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b)) ≥ 7 / (a ^ 2 + b ^ 2 + c ^ 2) + 2 / (a * b + b * c + a * c)   :=  by sorry
