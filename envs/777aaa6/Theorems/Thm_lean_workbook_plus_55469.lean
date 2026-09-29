-- Prove2me | Theorems.Thm_lean_workbook_plus_55469
-- name    : lean_workbook_plus_55469
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/33c7d1cc-1a5b-4cd2-9147-d637a5a9aeab
-- statement:
--   Show that, at the bottom of a vertical mine shaft dug to depth $D$, the measured value of $g$ will be $g=g_s(1-\frac{D}{R})$, $g_s$ being the surface value. Assume that the Earth is a uniform sphere of radius $R$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55469 (D : ℝ) (R : ℝ) (g_s : ℝ) (g : ℝ) (h₁ : R > D) (h₂ : g = g_s * (1 - D / R)) : g = g_s * (1 - D / R)   :=  by sorry
