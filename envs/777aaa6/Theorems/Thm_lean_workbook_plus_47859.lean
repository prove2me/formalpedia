-- Prove2me | Theorems.Thm_lean_workbook_plus_47859
-- name    : lean_workbook_plus_47859
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c1ccb860-9d4c-47e9-b36d-e72b287c5207
-- statement:
--   Prove that $2 > \tan\theta(1-\sin\theta)$ for $0 < \theta < \frac{\pi}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47859 (θ : ℝ) (h1 : 0 < θ) (h2 : θ < Real.pi / 2) : 2 > Real.tan θ * (1 - Real.sin θ)   :=  by sorry
