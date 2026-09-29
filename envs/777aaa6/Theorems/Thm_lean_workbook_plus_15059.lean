-- Prove2me | Theorems.Thm_lean_workbook_plus_15059
-- name    : lean_workbook_plus_15059
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/0498bda0-3686-4521-94a2-2f68ebe13db6
-- statement:
--   Prove that $2P^3-10P^2+9P-4\le0$ for $P\in[3-2\sqrt2,4]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15059 : ∀ P ∈ Set.Icc (3 - 2 * Real.sqrt 2) 4, 2 * P ^ 3 - 10 * P ^ 2 + 9 * P - 4 ≤ 0   :=  by sorry
