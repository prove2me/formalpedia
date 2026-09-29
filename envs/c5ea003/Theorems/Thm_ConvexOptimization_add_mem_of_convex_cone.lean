-- Prove2me | Theorems.Thm_ConvexOptimization_add_mem_of_convex_cone
-- name    : ConvexOptimization.add_mem_of_convex_cone
-- status  : Proved
-- author  : @jianglsbz
-- created : 2026-08-15T04:46:00.128069+00:00
-- url     : https://prove2.me/theorems/0a64aa6c-59e1-4d84-a5e0-73005522a114
-- title:
--   A convex cone is closed under addition
-- statement:
--   A convex cone contains every conic combination of its elements: Boyd and Vandenberghe note that for $x_1, x_2$ in a convex cone $C$ and $\theta_1, \theta_2 \ge 0$ one has $\theta_1 x_1 + \theta_2 x_2 \in C$. The case $\theta_1 = \theta_2 = 1$ is the additive closure recorded here.
--
--   Let $K \subseteq \mathbb{R}^d$ be convex and positively homogeneous, i.e. $t y \in K$ whenever $t > 0$ and $y \in K$. Then for all $u, v \in K$,
--
--   $$u + v \in K.$$
--
--   The proof is the standard two-step factorisation through the midpoint: convexity places $\tfrac{1}{2} u + \tfrac{1}{2} v$ in $K$, and scaling that midpoint by $2$ returns $u + v$. Neither hypothesis alone suffices — a nonconvex cone such as the union of two rays is not closed under addition, and a bounded convex set is not either.
--
--   Together with nonnegative scaling this is what makes a convex cone an additively closed structure, and it is the workhorse step whenever one checks that a vector assembled from several conic terms again lies in the cone.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 25, §2.1.5 (cones and conic combinations)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.add_mem_of_convex_cone {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKconv : Convex ℝ K)
    (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K)
    (u v : EuclideanSpace ℝ (Fin d)) (hu : u ∈ K) (hv : v ∈ K) :
    u + v ∈ K := by sorry
