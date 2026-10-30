-- Prove2me | Theorems.Thm_WilliamsonShmoys_joinedIn_has_injective_arc_metric__p2m_169c9a8e_df8f_41e3_a03b_f96007c76cfa_a1
-- name    : WilliamsonShmoys.joinedIn_has_injective_arc_metric__p2m_169c9a8e_df8f_41e3_a03b_f96007c76cfa_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:51:07.369562+00:00
-- url     : https://prove2.me/theorems/fbc04312-9eeb-4654-891c-ce7d8210aa33
-- title:
--   A path in a metric set contains an injective arc between distinct endpoints
-- statement:
--   Given a path from `x` to `y` whose image lies in `U`, this produces an injective continuous parametrization with the same endpoints and image in `U`. The distinct-endpoint hypothesis is essential: a constant path cannot yield an injective parametrization of the interval. A proof route is to work in the compact metric image of the given path and apply the theorem that a path-connected metric continuum contains an arc between any two distinct points, then reparametrize that arc on `[0,1]`. This removes arc extraction from the parent; the continuum-theoretic arc-extraction argument remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.joinedIn_has_injective_arc_metric__p2m_169c9a8e_df8f_41e3_a03b_f96007c76cfa_a1 {X : Type} [MetricSpace X] {U : Set X} {x y : X} (h : JoinedIn U x y) (hxy : x ≠ y) : ∃ γ : ℝ → X, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U := by sorry
