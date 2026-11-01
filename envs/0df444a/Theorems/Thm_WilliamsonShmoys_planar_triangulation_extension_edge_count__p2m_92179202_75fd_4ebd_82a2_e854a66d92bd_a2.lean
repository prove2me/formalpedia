-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_92179202_75fd_4ebd_82a2_e854a66d92bd_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_92179202_75fd_4ebd_82a2_e854a66d92bd_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:23:58.34806+00:00
-- url     : https://prove2.me/theorems/95f0e96c-588c-4293-a881-4eae330a335f
-- title:
--   Planar triangulation extension with exact edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_92179202_75fd_4ebd_82a2_e854a66d92bd_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      L.edgeSet ⊆ T.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
