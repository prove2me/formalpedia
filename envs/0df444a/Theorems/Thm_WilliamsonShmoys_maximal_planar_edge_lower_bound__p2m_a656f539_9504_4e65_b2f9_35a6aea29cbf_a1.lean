-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_a656f539_9504_4e65_b2f9_35a6aea29cbf_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_a656f539_9504_4e65_b2f9_35a6aea29cbf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:58:14.470835+00:00
-- url     : https://prove2.me/theorems/44ad9d62-d07a-45ba-9c4b-dda6b98dfb28
-- title:
--   Lower edge bound for an edge-maximal planar graph
-- statement:
--   An edge-maximal finite simple graph admitting a planar drawing on at least three vertices has at least 3|V|−6 edges. The maximality hypothesis is exactly the target's condition that no drawable graph on the same vertices can strictly contain its edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_a656f539_9504_4e65_b2f9_35a6aea29cbf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by sorry
