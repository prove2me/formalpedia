-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_incidence_for_euler_count
-- name    : WilliamsonShmoys.maximal_drawable_graph_incidence_for_euler_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:14:21.52684+00:00
-- url     : https://prove2.me/theorems/bb1e381f-3bfa-43e8-873d-4da72a56878c
-- title:
--   Triangular incidence equation for an Euler face count
-- statement:
--   For a maximal drawable simple graph on at least three vertices, any natural face count satisfying Euler’s equation also satisfies the triangular face-edge incidence equation. The independent proof route is to show maximality forces triangular face boundaries and count each edge on two face sides. The `hCard` bound excludes the small-vertex cases where this conclusion need not hold.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_incidence_for_euler_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → L = M)
    (hCard : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = L.edgeSet.ncard + 2) :
    3 * f = 2 * L.edgeSet.ncard := by sorry
