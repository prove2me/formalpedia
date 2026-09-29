-- Prove2me | Theorems.Thm_Hirsch_todd_bound
-- name    : Hirsch.todd_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:28:08.493071+00:00
-- url     : https://prove2.me/theorems/38c56b77-6a7b-4478-b089-0400d8c6cfff
-- title:
--   Todd: diameter at most $(n-d)^{\log_2 d}$
-- statement:
--   (Todd 2014.) Every full-dimensional (nonempty interior) bounded H-polytope in $\mathbb{R}^d$ with $n \ge d \ge 3$ inequalities has combinatorial diameter at most $(n - d)^{\log_2 d}$, sharpening the Kalai--Kleitman bound to a form matching the Hirsch quantity $n - d$ at its base. The formal bound is the natural floor of the real power; full-dimensionality and $n \ge d \ge 3$ are hypotheses of the source theorem and are assumed explicitly.
-- source:
--   Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, SIAM J. Discrete Math. 28 (2014) 1944-1947, https://arxiv.org/abs/1402.3579

import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem todd_bound (d n : ℕ) (hd : 3 ≤ d) (hdn : d ≤ n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (interior (Hpoly a b)).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) ⌊((n : ℝ) - d) ^ (Real.logb 2 d)⌋₊ := by sorry

end Hirsch
