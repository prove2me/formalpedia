-- Prove2me | Theorems.Thm_Hirsch_adj_of_synchronized_height_edges
-- name    : Hirsch.adj_of_synchronized_height_edges
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T08:56:51.568832+00:00
-- url     : https://prove2.me/theorems/299c84a2-47c7-472e-8d75-bbedcc835d42
-- title:
--   Synchronized factor edges are edges of the scalar-height fiber
-- statement:
--   Let $P_1,\dots,P_k\subseteq\mathbb R^d$ be convex sets with affine height functions $h_i$. Write $F$ for their common-height fiber: tuples $(x_i)$ with $x_i\in P_i$ and all $h_i(x_i)$ equal.
--
--   Suppose each factor has a genuine edge $[p_i,q_i]$, and two fiber points $a,b$ lie on those edges at common heights $H_0>H_1$, with every $p_i$ at height at least $H_0$ and every $q_i$ at height at most $H_1$. If some factor realizes the upper height exactly at $p_i$ and some factor realizes the lower height exactly at $q_i$, then the segment $[a,b]$ is an edge of $F$:
--
--   $$
--   \operatorname{Adj}(F, a, b).
--   $$
--
--   Height is strictly monotone on each factor edge, so a point of $F$ on the product of those edges is uniquely determined by its common height. Tight factors pin that height to the interval $[H_1,H_0]$, which is why a partial traversal of a longer edge remains extreme in the fiber.
--
--   This is the one-step geometric engine of the scalar-height fiber obstruction: strictly monotone factor paths synchronize to genuine fiber edges. It does not by itself bound unrestricted polytope diameter.
--
--   **Formalization Note** The ambient space of $F$ is the product $(\mathbb R^d)^k$. Boundedness of the $P_i$ is not assumed.
-- source:
--   Geometric step of the scalar-fiber obstruction in jjoshua2/prove2me-work PR #11 (2026-09-08); platform definition Hirsch_scalar_fiber_model (59af3151-06aa-45f7-a758-293ca1fc5a83). No literature-priority claim.

import Definitions.Def_Hirsch_scalar_fiber_model
set_option autoImplicit false
open Set Hirsch AffineMap

theorem Hirsch.adj_of_synchronized_height_edges {k d : ℕ}
    (P : Fin k → Set (EuclideanSpace ℝ (Fin d)))
    (hh : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ)
    (a b p q : Fin k → EuclideanSpace ℝ (Fin d))
    (H0 H1 : ℝ) (hlt : H1 < H0)
    (haH : ∀ i, hh i (a i) = H0)
    (hbH : ∀ i, hh i (b i) = H1)
    (hedge : ∀ i, Adj (P i) (p i) (q i))
    (haOn : ∀ i, a i ∈ segment ℝ (p i) (q i))
    (hbOn : ∀ i, b i ∈ segment ℝ (p i) (q i))
    (hpH : ∀ i, hh i (p i) ≥ H0)
    (hqH : ∀ i, hh i (q i) ≤ H1)
    (htight0 : ∃ i, hh i (p i) = H0)
    (htight1 : ∃ i, hh i (q i) = H1) :
    Adj (ScalarHeightFiber P hh) a b := by sorry
