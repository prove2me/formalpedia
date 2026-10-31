-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulated_supergraph_edge_bound__p2m_0b3a5bc9_5212_4922_863b_b35f1f108c76_a1
-- name    : WilliamsonShmoys.planar_triangulated_supergraph_edge_bound__p2m_0b3a5bc9_5212_4922_863b_b35f1f108c76_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:02:13.782201+00:00
-- url     : https://prove2.me/theorems/12adc1a9-2da3-4bce-a578-d16f94d48e85
-- title:
--   Planar triangulated supergraph edge bound
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulated_supergraph_edge_bound__p2m_0b3a5bc9_5212_4922_863b_b35f1f108c76_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
