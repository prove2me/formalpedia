-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound__p2m_bc33823c_9eaa_4787_b342_ad6547a0cb58_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_bc33823c_9eaa_4787_b342_ad6547a0cb58_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:36:04.177428+00:00
-- url     : https://prove2.me/theorems/6d3b2982-65b7-41de-b042-0682b8cb7f57
-- title:
--   Planar supergraphs attain the maximal planar edge lower bound
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with at least 3|V|−6 edges. This follows by extending a drawing to a triangulation and counting edges using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_bc33823c_9eaa_4787_b342_ad6547a0cb58_a1
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
      3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by sorry
