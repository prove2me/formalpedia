-- Prove2me | Theorems.Thm_lean_workbook_plus_34131
-- name    : lean_workbook_plus_34131
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/a4213027-5222-4e92-80fb-de230ecfadab
-- statement:
--   Prove that \(\sqrt{2}e^{x}\cos \left(x - \frac{\pi}{4} \right) = e^{x} \left(\sin x + \cos x \right)\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34131 : ∀ x : ℝ, Real.sqrt 2 * Real.exp x * Real.cos (x - π / 4) = Real.exp x * (Real.sin x + Real.cos x)   :=  by sorry
