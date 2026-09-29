-- Prove2me | Theorems.Thm_lean_workbook_plus_21262
-- name    : lean_workbook_plus_21262
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/944f1bbf-a413-465f-b9b3-b6d83c621536
-- statement:
--   prove $abc(xy+yz+zx)\ge xyz(ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21262 : ∀ a b c x y z : ℝ, a * b * c * (x * y + y * z + z * x) ≥ x * y * z * (a * b + b * c + c * a)   :=  by sorry
