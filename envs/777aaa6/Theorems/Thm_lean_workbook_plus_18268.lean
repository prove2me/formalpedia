-- Prove2me | Theorems.Thm_lean_workbook_plus_18268
-- name    : lean_workbook_plus_18268
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8c1fe788-0644-4b9e-98a8-b33844f85500
-- statement:
--   $ 12000=H-\frac{1}{5}H \implies H=15000$ . $ 12000=S+\frac{1}{5}S \implies S=10000 \implies H+S=25000$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18268  (h s : ℝ)
  (h₀ : h - 1 / 5 * h = 12000)
  (h₁ : s + 1 / 5 * s = 12000) :
  h + s = 25000   :=  by sorry
