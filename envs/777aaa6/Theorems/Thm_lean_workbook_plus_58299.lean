-- Prove2me | Theorems.Thm_lean_workbook_plus_58299
-- name    : lean_workbook_plus_58299
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/9acfc8fc-6fa2-4885-9a16-803e0621ea0d
-- statement:
--   (t-s)^2 \ge t-s for integers \(t\) and \(s\) with \(t \geq s\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58299 (t s : ℤ) (h₁ : t ≥ s) (h₂ : t ≤ s) : (t - s)^2 ≥ t - s   :=  by sorry
