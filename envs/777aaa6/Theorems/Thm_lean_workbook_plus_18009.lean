-- Prove2me | Theorems.Thm_lean_workbook_plus_18009
-- name    : lean_workbook_plus_18009
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/ed6dca80-b2da-4bea-ae00-d8dbdd3950e8
-- statement:
--   证明：若 \( x^2+y^2 \geq \frac{1}{2} \) 且 \( xy \leq \frac{1}{4} \)，则 \( 2(x^2+y^2)^5 \geq \frac{1}{16} \geq (xy)^2 \)。
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18009 : x^2 + y^2 ≥ 1 / 2 ∧ x * y ≤ 1 / 4 → 2 * (x^2 + y^2)^5 ≥ 1 / 16 ∧ 1 / 16 ≥ (x * y)^2   :=  by sorry
