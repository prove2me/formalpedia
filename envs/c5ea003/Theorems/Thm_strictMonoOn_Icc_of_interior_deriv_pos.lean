-- Prove2me | Theorems.Thm_strictMonoOn_Icc_of_interior_deriv_pos
-- name    : strictMonoOn_Icc_of_interior_deriv_pos
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T19:03:17.144127+00:00
-- url     : https://prove2.me/theorems/cb4f43dc-8448-4527-af14-d33e113f7a5d
-- title:
--   Strict monotonicity on $[a,b]$ from a positive interior derivative
-- statement:
--   If $f$ is continuous on the closed interval $[a,b]$ and has a strictly positive derivative $f'$ at every **interior** point $x\in(a,b)$ — with no derivative requirement at the endpoints — then $f$ is strictly increasing on $[a,b]$. This is the boundary-aware form of monotonicity-from-positive-derivative: it applies to functions such as $t\mapsto \log(g\,t)$ that are well-defined and differentiable only on the open interval. Source: standard real-analysis consequence of the mean value theorem; in Mathlib it follows from `strictMonoOn_of_deriv_pos` (Mathlib/Analysis/Calculus/Deriv/MeanValue.lean), which requires only `ContinuousOn f D` and positivity of `deriv f` on `interior D`.
-- source:
--   Standard real analysis (mean value theorem); Mathlib strictMonoOn_of_deriv_pos.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
open Set

theorem strictMonoOn_Icc_of_interior_deriv_pos (f f' : ℝ → ℝ) (a b : ℝ) (hcont : ContinuousOn f (Set.Icc a b)) (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f' x) : StrictMonoOn f (Set.Icc a b) := by sorry
