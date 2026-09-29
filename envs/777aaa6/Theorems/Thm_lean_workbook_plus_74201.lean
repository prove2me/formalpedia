-- Prove2me | Theorems.Thm_lean_workbook_plus_74201
-- name    : lean_workbook_plus_74201
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/0c4d752a-8bb7-4b79-b505-cb5348fcb369
-- statement:
--   Express $ cos4\theta, sin4\theta$ in terms of powers of $ cos\theta$ and $ sin\theta$ and show that $ tan4\theta =\frac{4tan\theta-4tan^{3}\theta}{1-6tan^{2}\theta+tan^{4}\theta}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74201 : ∀ θ : ℝ, cos 4*θ = 8 * cos θ ^ 4 - 8 * cos θ ^ 2 + 1 ∧ sin 4*θ = 4 * sin θ ^ 3 * cos θ ∧ tan 4*θ = (4 * tan θ - 4 * tan θ ^ 3) / (1 - 6 * tan θ ^ 2 + tan θ ^ 4)   :=  by sorry
