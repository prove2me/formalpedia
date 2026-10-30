-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_eq_of_maximal_planar_729fc1e5
-- name    : WilliamsonShmoys.edge_count_eq_of_maximal_planar_729fc1e5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:56:55.457884+00:00
-- url     : https://prove2.me/theorems/efbfc9b8-3ee5-450e-bfac-b41d2c2bb5f3
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strict drawable supergraph on the same vertices has exactly 3|V|−6 edges. The proof requires showing maximality forces a triangulation and then applying the planar Euler edge count; this is the core topological obligation left for the child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_eq_of_maximal_planar_729fc1e5
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ S : SimpleGraph V, R ≤ S →
      WilliamsonShmoys.HasPlanarDrawingOn S → S = R) :
    R.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
