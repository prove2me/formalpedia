-- Prove2me | Theorems.Thm_lean_workbook_plus_80262
-- name    : lean_workbook_plus_80262
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/5c6b24c1-dcf9-426a-a614-419f4e12124e
-- statement:
--   Let $f:\mathbb{N}\rightarrow \mathbb{N}$ be a function satisfies the following condition $f\left ( xy+1 \right )=xf\left ( y \right )+2012\quad \forall x,y\in \mathbb{N}$. Prove that $\sum_{i=1}^{2012}f^{3}\left ( i \right )>\frac{1}{4}\left ( 2012 \right )^{7}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80262 (f : ℕ → ℕ) (hf: ∀ x y : ℕ, f (xy + 1) = x * f y + 2012): ∑ i in Finset.range 2012, (f i)^3 > (1/4) * (2012)^7   :=  by sorry
