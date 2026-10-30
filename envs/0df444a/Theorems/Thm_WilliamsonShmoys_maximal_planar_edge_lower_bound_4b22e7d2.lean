-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_4b22e7d2
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_4b22e7d2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:04:56.223165+00:00
-- url     : https://prove2.me/theorems/22dca8d1-eedd-4092-b1df-e60bc452db63
-- title:
--   Lower edge bound for a maximal planar graph
-- statement:
--   A graph maximal under edge inclusion among graphs with the supplied planar drawing, with at least three vertices, has at least \(3|V|-6\) edges. The independent proof route establishes connectedness and triangular faces from maximality, then applies Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_4b22e7d2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H →
      G.edgeSet ⊆ H.edgeSet →
      H.edgeSet ⊆ G.edgeSet) :
    3 * Fintype.card V - 6 ≤ G.edgeSet.ncard := by sorry
