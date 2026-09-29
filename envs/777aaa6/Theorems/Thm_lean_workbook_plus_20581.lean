-- Prove2me | Theorems.Thm_lean_workbook_plus_20581
-- name    : lean_workbook_plus_20581
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/bb86284d-b29d-41b1-890b-963e39deab35
-- statement:
--   $f(0)=f(\sqrt5)=-1\Longrightarrow f(t)\le-1, \forall t\in[0,\sqrt5]\Longrightarrow$\n $\Longrightarrow |f(t)|\ge1, \forall t\in[0,\sqrt5]$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20581  (f : ℝ → ℝ)
  (h₀ : f 0 = -1)
  (h₁ : f (Real.sqrt 5) = -1)
  (h₂ : ∀ t ∈ Set.Icc 0 (Real.sqrt 5), f t ≤ -1) :
  ∀ t ∈ Set.Icc 0 (Real.sqrt 5), 1 ≤ |f t|   :=  by sorry
