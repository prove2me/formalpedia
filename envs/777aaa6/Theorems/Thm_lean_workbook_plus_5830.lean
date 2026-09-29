-- Prove2me | Theorems.Thm_lean_workbook_plus_5830
-- name    : lean_workbook_plus_5830
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/f09a3785-dd86-4a9f-8d30-f3754ffa6532
-- statement:
--   d) $\frac{1}{2}+\cos \theta +\cos \left( 2\theta \right)+...+\cos \left( n\theta \right)=\frac{\sin \left[ \frac{\left( 2n+1 \right)\theta }{2} \right]}{2\sin \left( \frac{\theta }{2} \right)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5830 :
  ∀ n : ℕ, ∀ θ : ℝ, ∑ k in Finset.range (n+1), cos (k * θ) =
    sin ((2 * n + 1) * θ / 2) / (2 * sin (θ / 2))   :=  by sorry
