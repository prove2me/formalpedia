-- Prove2me | Theorems.Thm_lean_workbook_plus_36139
-- name    : lean_workbook_plus_36139
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/47fbf026-98ce-4b0f-ac57-214b8380dbaa
-- statement:
--   Find the value of $\tan{x}$ if $\sin{x}+\cos{x}=\frac{1}{5}$ and $\frac{\pi}{2}<x<\pi$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36139 (x : ℝ) (hx : π/2 < x ∧ x < π) (h : sin x + cos x = 1/5) : tan x = -4/3   :=  by sorry
