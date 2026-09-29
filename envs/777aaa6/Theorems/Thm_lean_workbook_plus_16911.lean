-- Prove2me | Theorems.Thm_lean_workbook_plus_16911
-- name    : lean_workbook_plus_16911
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/fde26885-8d8a-4a21-9391-5ec5643c8d92
-- statement:
--   Show that $3v^2+w^3<2$ if $u<\sqrt{3}-1$, $v<\sqrt{3}-1$, and $w<\sqrt{3}-1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16911 : ∀ u v w : ℝ, u < (Real.sqrt 3) - 1 ∧ v < (Real.sqrt 3) - 1 ∧ w < (Real.sqrt 3) - 1 → 3 * v ^ 2 + w ^ 3 < 2   :=  by sorry
