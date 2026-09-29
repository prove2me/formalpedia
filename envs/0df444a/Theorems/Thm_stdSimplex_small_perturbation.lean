-- Prove2me | Theorems.Thm_stdSimplex_small_perturbation
-- name    : stdSimplex_small_perturbation
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:23:18.784037+00:00
-- url     : https://prove2.me/theorems/33ec3c2c-7aab-42bb-9820-66015a39b209
-- title:
--   Small zero-sum perturbations preserve a strictly positive simplex point
-- statement:
--   Let $u$ be a probability vector whose coordinates are all strictly positive, and let $q\in\mathbb R^d$ have zero coordinate sum. Then there is a radius $\delta>0$ such that every perturbation $u+\Delta q$ with $|\Delta|\le\delta$ is again a probability vector:
--
--   $$
--   \exists\delta>0\;\forall |\Delta|\le\delta,\qquad u+\Delta q\in\mathcal P_{d-1}.
--   $$
--
--   In particular, both $u-\Delta q$ and $u+\Delta q$ remain valid stochastic environments for sufficiently small $\Delta$. This is the simplex-interiority step in two-environment information-theoretic lower bounds.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), Theorem 37.12, Step 1, printed p. 490, paragraph surrounding Eq. (37.7).

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

theorem stdSimplex_small_perturbation
    {d : ℕ} (u q : Fin d → ℝ)
    (hu : u ∈ stdSimplex ℝ (Fin d))
    (hupos : ∀ i, 0 < u i) (hq : ∑ i, q i = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Δ : ℝ, |Δ| ≤ δ →
      (fun i ↦ u i + Δ * q i) ∈ stdSimplex ℝ (Fin d) := by sorry
