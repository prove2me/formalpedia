-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_6d3b2982_65b7_41de_b042_0682b8cb7f57_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_6d3b2982_65b7_41de_b042_0682b8cb7f57_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:48:28.2204+00:00
-- url     : https://prove2.me/theorems/6d23e6d9-3a8b-46d0-86a1-79ef2bae4d90
-- title:
--   Edge bound for a maximum drawable graph
-- statement:
--   A drawable simple graph on at least three vertices whose edge count is maximal among drawable supergraphs has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_6d3b2982_65b7_41de_b042_0682b8cb7f57_a1
    {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hMax : ∀ Q : SimpleGraph V,
      P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q →
        Q.edgeSet.ncard ≤ P.edgeSet.ncard) :
    3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by sorry
