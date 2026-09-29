-- Prove2me | Theorems.Thm_lean_workbook_plus_3175
-- name    : lean_workbook_plus_3175
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/beba1b69-976a-4e36-8450-abeea00ea892
-- statement:
--   $(x^{2n + 2} - y^{2n + 2}) = (x^{2n} - y^{2n})x^2 + y^{2n}(x^2 - y^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3175 (x y : ℝ) (n : ℕ) : (x^(2 * n + 2) - y^(2 * n + 2)) = (x^(2 * n) - y^(2 * n)) * x^2 + y^(2 * n) * (x^2 - y^2)   :=  by sorry
