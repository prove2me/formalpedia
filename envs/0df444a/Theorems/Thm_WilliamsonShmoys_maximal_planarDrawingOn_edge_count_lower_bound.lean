-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planarDrawingOn_edge_count_lower_bound
-- name    : WilliamsonShmoys.maximal_planarDrawingOn_edge_count_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:53:51.682605+00:00
-- url     : https://prove2.me/theorems/7968fb84-5370-431f-b5f9-123d758521dd
-- title:
--   Maximal planar drawing edge-count lower bound
-- statement:
--   A drawable graph on at least three vertices that has no drawable strict supergraph on the same vertex type has at least 3|V|−6 edges. The proof route is to establish that every face in the drawing is triangular: a non-triangular face permits adding a diagonal while preserving planarity, contradicting maximality. Euler’s formula and face-edge incidence counting then give the bound. This isolates the maximality/triangulation direction from the general planar upper bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planarDrawingOn_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊂ N.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn N) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
