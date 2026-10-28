-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_supergraph_54a0e51c
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_supergraph_54a0e51c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T12:43:54.431115+00:00
-- url     : https://prove2.me/theorems/cb19d0be-e578-4657-8ef2-f6d226382bed
-- title:
--   Edge count of a maximal planar supergraph for this extension theorem
-- statement:
--   A drawable supergraph containing every drawable supergraph of L has exactly 3n − 6 edges when the vertex type has at least three elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_supergraph_54a0e51c
    {V : Type} [Fintype V] [LinearOrder V]
    (L M : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hLM : L.edgeSet ⊆ M.edgeSet)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      L.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
