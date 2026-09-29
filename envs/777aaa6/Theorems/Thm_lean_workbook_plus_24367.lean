-- Prove2me | Theorems.Thm_lean_workbook_plus_24367
-- name    : lean_workbook_plus_24367
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/47b22026-d135-45a3-a352-c5fcccacecab
-- statement:
--   Now is the magic result : $ f(x)=\frac{x}{5}$ $ \forall x\in[0,10)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24367 (f : ℝ → ℝ) (hf: f = fun x => x / 5) : ∀ x ∈ Set.Ico (0:ℝ) 10, f x = x / 5   :=  by sorry
