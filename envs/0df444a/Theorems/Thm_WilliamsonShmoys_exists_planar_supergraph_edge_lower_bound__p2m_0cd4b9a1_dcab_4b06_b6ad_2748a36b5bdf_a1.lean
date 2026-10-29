-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_lower_bound__p2m_0cd4b9a1_dcab_4b06_b6ad_2748a36b5bdf_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_edge_lower_bound__p2m_0cd4b9a1_dcab_4b06_b6ad_2748a36b5bdf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T00:56:41.615825+00:00
-- url     : https://prove2.me/theorems/63ca304f-09ca-4fb0-945d-2eb65f783053
-- title:
--   Planar supergraph edge lower bound
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph with at least 3|V|−6 edges. This packages planar completion and the Euler edge count into a reusable result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_edge_lower_bound__p2m_0cd4b9a1_dcab_4b06_b6ad_2748a36b5bdf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
