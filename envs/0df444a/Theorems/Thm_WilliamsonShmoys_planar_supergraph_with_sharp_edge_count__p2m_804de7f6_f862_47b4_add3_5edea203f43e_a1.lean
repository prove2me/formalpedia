-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_sharp_edge_count__p2m_804de7f6_f862_47b4_add3_5edea203f43e_a1
-- name    : WilliamsonShmoys.planar_supergraph_with_sharp_edge_count__p2m_804de7f6_f862_47b4_add3_5edea203f43e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:44:09.694207+00:00
-- url     : https://prove2.me/theorems/261600ee-7fa4-4a45-a37b-002442c9d475
-- title:
--   Planar extension with sharp edge count
-- statement:
--   Every finite planar graph on at least three vertices has a planar supergraph on the same vertex set with exactly 3|V|−6 edges. The parent uses maximality to show that this extension is equal to the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_with_sharp_edge_count__p2m_804de7f6_f862_47b4_add3_5edea203f43e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
