-- Prove2me | Theorems.Thm_lean_workbook_plus_45771
-- name    : lean_workbook_plus_45771
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/bb70208d-37bc-4e29-84a8-8711b9c3ce48
-- statement:
--   $\frac {a^2}{4bc}\geq \left(\frac {a}{b + c}\right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45771 : ∀ a b c : ℝ, a^2 / (4 * b * c) ≥ (a / (b + c))^2   :=  by sorry
