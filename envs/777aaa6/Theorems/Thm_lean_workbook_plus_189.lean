-- Prove2me | Theorems.Thm_lean_workbook_plus_189
-- name    : lean_workbook_plus_189
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/615c883c-093e-4cca-a1ff-4fbb6d41222e
-- statement:
--   Prove that if $f(av)=af(v)$ and $f(v+w)=f(v)+f(w)$ for all $a, v, w \in \mathbb{R}$, then $f$ is a linear function of the form $f(x) = cx$ for some constant $c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_189 (f : ℝ → ℝ) (hf: ∀ a v w : ℝ, f (a * v) = a * f v ∧ f (v + w) = f v + f w) : ∃ c :ℝ, ∀ x : ℝ, f x = c * x   :=  by sorry
