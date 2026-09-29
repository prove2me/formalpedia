-- Prove2me | Theorems.Thm_lean_workbook_plus_46630
-- name    : lean_workbook_plus_46630
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ab0342ce-0ea5-4da0-b13c-44301eb8eda8
-- statement:
--   Where $a^2+b^2+c^2\ge \frac{1}{3}(a+b+c)^2\iff a^2+b^2+c^2\ge bc+ca+ab$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46630 : ∀ a b c : ℝ, a^2 + b^2 + c^2 ≥ (1 / 3) * (a + b + c)^2 ↔ a^2 + b^2 + c^2 ≥ b * c + c * a + a * b   :=  by sorry
