-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_on_edge_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_on_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:36:48.468747+00:00
-- url     : https://prove2.me/theorems/0dc5c5ac-c337-4be4-9c1c-064758e763e2
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A finite simple graph with at least three vertices whose planar drawing admits no strict planar supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_on_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
