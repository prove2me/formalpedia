-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph
-- name    : WilliamsonShmoys.planar_triangulation_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:50:59.591694+00:00
-- url     : https://prove2.me/theorems/024b7900-54e2-459e-be4a-3541b5b5af4e
-- title:
--   Triangulate a planar drawing on the same vertices
-- statement:
--   Extend the supplied planar drawing to a triangulated planar supergraph on the same vertex set, whose edge count satisfies Euler’s triangulation equality. The inclusion makes the target edge bound follow by monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
