-- Prove2me | Theorems.Thm_lean_workbook_plus_36620
-- name    : lean_workbook_plus_36620
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d5abfef3-3589-4908-8ae3-99e424ed0a61
-- statement:
--   Prove: $\sin{2\theta}=\frac{2}{\tan{\theta}+\cot{\theta}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36620 (θ : ℝ) : sin (2 * θ) = 2 / (tan θ + 1 / tan θ)   :=  by sorry
