-- Prove2me | Theorems.Thm_lean_workbook_plus_34190
-- name    : lean_workbook_plus_34190
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/3236548c-478f-45c3-bf4d-782acf9f54d0
-- statement:
--   Let the original price be $ x$ . We have $ (1+\frac{p}{100})(1-\frac{p}{100})x=1$ . Hence, $ x=\frac{1}{1-(\frac{p}{100})^2}=\frac {10000}{10000 - p^2}$ , or $ \textbf{(E)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34190  (x p : ℝ)
  (h₀ : 0 < x ∧ 0 < p)
  (h₁ : (1 + p / 100) * (1 - p / 100) * x = 1) :
  x = 10000 / (10000 - p^2)   :=  by sorry
