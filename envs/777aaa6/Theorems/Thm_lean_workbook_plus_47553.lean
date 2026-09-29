-- Prove2me | Theorems.Thm_lean_workbook_plus_47553
-- name    : lean_workbook_plus_47553
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/af664daa-360e-42a6-b467-af2734aba847
-- statement:
--   As $\sin^2 x=\frac 12-\frac 12 \cos 2x$,\nWe have $\sin^2 x\sin nx=(\frac 12-\frac 12 \cos 2x)\sin nx=\frac 12 \sin nx-\frac 12\sin nx \cos 2x=\frac 14(2\sin nx-\sin (n+2)x-\sin (n-2)x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47553 : ∀ n : ℕ, ∀ x : ℝ, (Real.sin x)^2 * Real.sin (n * x) = 1/4 * (2 * Real.sin (n * x) - Real.sin ((n + 2) * x) - Real.sin ((n - 2) * x))   :=  by sorry
