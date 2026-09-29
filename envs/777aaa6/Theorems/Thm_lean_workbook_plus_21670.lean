-- Prove2me | Theorems.Thm_lean_workbook_plus_21670
-- name    : lean_workbook_plus_21670
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/3a2779d2-784b-45db-92ee-9ba63849e04c
-- statement:
--   This is equivalent to: $$4a^4+4b^4+4c^4\ge4a^2b^2+4b^2c^2+4c^2a^2,$$ or $$a^4+b^4+c^4\ge a^2b^2+b^2c^2+c^2a^2,$$ which is true by AM-GM. ( $\frac{a^4}{2}+\frac{b^4}{2}\ge2\sqrt{\frac{a^4b^4}{4}}=a^2b^2.$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21670 : ∀ a b c : ℝ, 4 * a ^ 4 + 4 * b ^ 4 + 4 * c ^ 4 ≥ 4 * a ^ 2 * b ^ 2 + 4 * b ^ 2 * c ^ 2 + 4 * c ^ 2 * a ^ 2   :=  by sorry
