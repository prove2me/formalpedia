-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_under_drawing_584c8b76_bd83_4573_8170_cd34643c6778
-- name    : WilliamsonShmoys.planar_supergraph_maximal_under_drawing_584c8b76_bd83_4573_8170_cd34643c6778
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:21:53.146089+00:00
-- url     : https://prove2.me/theorems/a38c367b-252a-4040-9b94-c3edf03c1aaf
-- title:
--   Maximal planar supergraph under the supplied drawing predicate
-- statement:
--   Any finite graph with the supplied planar drawing is contained in a planar supergraph on the same ordered vertex type that is maximal under edge inclusion among graphs satisfying that drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_under_drawing_584c8b76_bd83_4573_8170_cd34643c6778
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊆ N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet ⊆ M.edgeSet := by sorry
