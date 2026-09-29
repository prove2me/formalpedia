-- Prove2me | Theorems.Thm_lean_workbook_plus_77770
-- name    : lean_workbook_plus_77770
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a1e0c9f1-2473-47ee-acc3-047e0d6f0b87
-- statement:
--   $ C-B = m^2 - 2mn + n^2 - 1 = (m-n)^2-1 \qquad(2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77770 (m n : ℤ) : (m - n) ^ 2 - 1 = m ^ 2 - 2 * m * n + n ^ 2 - 1   :=  by sorry
