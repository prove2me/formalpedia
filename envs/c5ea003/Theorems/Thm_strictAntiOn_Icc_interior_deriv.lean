-- Prove2me | Theorems.Thm_strictAntiOn_Icc_interior_deriv
-- name    : strictAntiOn_Icc_interior_deriv
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T20:22:04.862817+00:00
-- url     : https://prove2.me/theorems/30ae0fd6-6ac1-4318-87ed-9e75f544521c
-- title:
--   Strict antitonicity on $[a,b]$ from a negative interior derivative
-- statement:
--   **Boundary-aware strict antitonicity from an interior negative derivative.** If $f$ is continuous on $[a,b]$ and has derivative $f'(x)<0$ at every *interior* point $x\in(a,b)$ (no differentiability required at the endpoints), then $f$ is strictly decreasing on the closed interval $[a,b]$. This is the antitone sibling of `strictMonoOn_Icc_interior_deriv`; it applies to functions that blow up at an endpoint (e.g. log-densities) where only interior derivative information is available.
-- source:
--   Mathlib: strictAntiOn_of_deriv_neg + interior_Icc + HasDerivAt.deriv (Analysis.Calculus.Deriv.MeanValue).

import Mathlib.Analysis.Calculus.Deriv.MeanValue
open Set

theorem strictAntiOn_Icc_interior_deriv (f f' : ℝ → ℝ) (a b : ℝ) (hcont : ContinuousOn f (Set.Icc a b)) (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (hneg : ∀ x ∈ Set.Ioo a b, f' x < 0) : StrictAntiOn f (Set.Icc a b) := by sorry
