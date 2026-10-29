-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing__p2m_68514819_a212_4a71_843f_93b3ee5d7783_a2
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_68514819_a212_4a71_843f_93b3ee5d7783_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:12:20.02813+00:00
-- url     : https://prove2.me/theorems/765437cc-485f-4e8f-af25-7c07ec446d00
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_68514819_a212_4a71_843f_93b3ee5d7783_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
