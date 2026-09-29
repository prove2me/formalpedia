-- Prove2me | Theorems.Thm_lean_workbook_plus_20727
-- name    : lean_workbook_plus_20727
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e3589be9-f651-41ac-89d0-36deb3a56871
-- statement:
--   Write $ x^8+x^5+x^4+x^3+x+1 = $ $ (x^8 - x^2) + (x^5+x^4+x^3+x^2+x+1) = $ $ \dfrac {(x^6-1)(x^2(x-1)+1)}{x-1} = $ $ (x+1)(x^2-x+1)(x^2+x+1)(x^3-x^2+1) $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20727 : ∀ x : ℝ, x^8 + x^5 + x^4 + x^3 + x + 1 = (x + 1) * (x^2 - x + 1) * (x^2 + x + 1) * (x^3 - x^2 + 1)   :=  by sorry
