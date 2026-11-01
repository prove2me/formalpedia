-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_6683070b_8f0f_4f85_989e_81cd2560323f_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6683070b_8f0f_4f85_989e_81cd2560323f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:52:42.628669+00:00
-- url     : https://prove2.me/theorems/a4df0ed7-7cc8-4f60-8566-0ad346baef91
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that has no drawable strict supergraph on the same vertex set has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6683070b_8f0f_4f85_989e_81cd2560323f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ N.edgeSet) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
