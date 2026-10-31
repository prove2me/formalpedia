-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_3e16b919_4c6f_4ffa_b173_33b0ad744e42_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_3e16b919_4c6f_4ffa_b173_33b0ad744e42_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:53:25.802175+00:00
-- url     : https://prove2.me/theorems/72da0c4c-c453-4f91-8db7-dbd4898e7c1c
-- title:
--   Edge lower bound for maximal drawable graphs
-- statement:
--   An edge-maximal drawable simple graph on at least three finite vertices has at least 3n−6 edges. Prove by extending the drawing to a triangulation and applying Euler’s formula, then use maximality to identify the extension with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_3e16b919_4c6f_4ffa_b173_33b0ad744e42_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet = M.edgeSet) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
