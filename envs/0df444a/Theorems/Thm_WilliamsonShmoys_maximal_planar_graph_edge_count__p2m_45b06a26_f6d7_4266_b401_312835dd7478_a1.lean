-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:02:05.436897+00:00
-- url     : https://prove2.me/theorems/8c6de935-4f5b-49ef-8949-a6af2a37957f
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
