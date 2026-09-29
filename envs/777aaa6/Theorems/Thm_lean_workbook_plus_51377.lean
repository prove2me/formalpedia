-- Prove2me | Theorems.Thm_lean_workbook_plus_51377
-- name    : lean_workbook_plus_51377
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/a9a9622b-6100-494f-817d-ee224fadfff0
-- statement:
--   The distance the tuna travels in time $t$ is $t \times 13.5 = d_{1}$ The distance the shark travels in time $t$ is $(t-7)\times15 = d_{2}$ ( I guess it's only true if t is greater than 7) When the shark catches the tuna they both will have traveled the same distance so that $d_{1} = d_{2}$ . So if I equate the two equations I can solve for $t$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51377 (t : ℝ) (d₁ d₂ : ℝ) (h₁ : d₁ = t * 13.5) (h₂ : d₂ = (t-7) * 15) : d₁ = d₂ ↔ t = 70   :=  by sorry
