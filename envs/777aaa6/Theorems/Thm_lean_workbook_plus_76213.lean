-- Prove2me | Theorems.Thm_lean_workbook_plus_76213
-- name    : lean_workbook_plus_76213
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/22af1221-83bb-4973-9bbb-8e0df31bed95
-- statement:
--   If $ f(1/2)=f(1/4)$ or $ f(1/2)=f(3/4)$ then f is not injective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76213 (f : ℝ → ℝ) (hf: f (1 / 2) = f (1 / 4) ∨ f (1 / 2) = f (3 / 4)) : ¬ Function.Injective f   :=  by sorry
