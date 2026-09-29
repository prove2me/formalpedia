-- Prove2me | Theorems.Thm_lean_workbook_plus_1331
-- name    : lean_workbook_plus_1331
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/bbd60c9c-0cd3-4caf-9981-81e35df97c85
-- statement:
--   For $n\ge 1$ : $0<\frac{\pi}{n+1}<\frac{\pi}n\le\pi$ and so, since $\cos x$ is decreasing over $[0,\pi]$ : $\cos\frac{\pi}{n+1}>\cos \frac{\pi}n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1331 (n : ℕ) (hn : 1 ≤ n) : Real.cos (π / (n + 1)) > Real.cos (π / n)   :=  by sorry
