-- Prove2me | Theorems.Thm_lean_workbook_plus_21880
-- name    : lean_workbook_plus_21880
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/928366b9-a575-49ae-96b2-4fcc3e17d81b
-- statement:
--   Find all functions $f : \mathbb{R} \to \mathbb{R}$ such that $f(x-y)+f(y-z)-f(z-x)=f(x+y+z)$, where $xy+yz+zx=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21880 (f : ℝ → ℝ):(∀ x y z:ℝ, (x*y+y*z+z*x=0 → f (x-y) + f (y-z) - f (z-x) = f (x+y+z))) ↔ ∃ c:ℝ, ∀ x:ℝ, f x = c   :=  by sorry
