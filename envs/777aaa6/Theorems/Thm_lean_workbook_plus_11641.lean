-- Prove2me | Theorems.Thm_lean_workbook_plus_11641
-- name    : lean_workbook_plus_11641
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/78d73165-bf56-45a2-be48-20adab0de8f2
-- statement:
--   By $AM-GM$ inequality, we have $a^2+4b^2\ge 2\sqrt{a^2\cdot 4b^2}=4ab\Rightarrow a^2+4b^2-4ab\ge 0.~~~(I)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11641 (a b : ℝ) : a ^ 2 + 4 * b ^ 2 - 4 * a * b ≥ 0   :=  by sorry
