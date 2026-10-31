-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_has_lower_bound_supergraph__p2m_669e4dc4_1d9e_4965_8c14_0e14e949cb06_a1
-- name    : WilliamsonShmoys.planar_drawable_has_lower_bound_supergraph__p2m_669e4dc4_1d9e_4965_8c14_0e14e949cb06_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:45:39.282618+00:00
-- url     : https://prove2.me/theorems/3ee6bacb-2bd6-4aaa-b06f-7ea404afd915
-- title:
--   Planar supergraph with the planar edge lower bound
-- statement:
--   Every drawable simple graph on at least three vertices is a subgraph, on the same vertex set, of a drawable graph with at least 3|V|−6 edges. This preserves the three-vertex cutoff and assumes no connectedness of the input graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_has_lower_bound_supergraph__p2m_669e4dc4_1d9e_4965_8c14_0e14e949cb06_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  sorry
