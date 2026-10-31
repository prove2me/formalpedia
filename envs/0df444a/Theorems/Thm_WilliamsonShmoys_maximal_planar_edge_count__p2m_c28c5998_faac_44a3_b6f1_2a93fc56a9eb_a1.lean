-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:51:29.264082+00:00
-- url     : https://prove2.me/theorems/94c3c327-8601-4c2d-adbc-08897459bc6e
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite simple graph with at least three vertices that is maximal among planar supergraphs on its vertex type has exactly 3|V|−6 edges. The hypothesis explicitly quantifies over all planar supergraphs, which is the maximality property produced by the extension lemma.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
