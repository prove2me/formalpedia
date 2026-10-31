-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:45:18.515542+00:00
-- url     : https://prove2.me/theorems/bf9be5f4-efbc-4928-a7c5-3fcb68a1a21a
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   A drawable graph on at least three vertices that admits no strictly larger drawable supergraph on the same vertex type has at least 3n−6 edges. A proof can show that maximality forces every face to be triangular, then combine triangular face-edge incidence with Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) : 3 * Fintype.card V - 6 ≤ S.edgeSet.ncard := by sorry
