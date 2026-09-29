-- Prove2me | Theorems.Thm_lean_workbook_plus_80602
-- name    : lean_workbook_plus_80602
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/675bf78a-8a05-4bcc-8e40-ca588a10c9e4
-- statement:
--   Prove that: $\frac{a}{a^2 + 4} \leq \frac{2 + 3a}{25}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80602 : ∀ a : ℝ, a / (a ^ 2 + 4) ≤ (2 + 3 * a) / 25   :=  by sorry
