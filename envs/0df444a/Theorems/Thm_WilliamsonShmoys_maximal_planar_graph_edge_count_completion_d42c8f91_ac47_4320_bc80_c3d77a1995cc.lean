-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:51:02.486136+00:00
-- url     : https://prove2.me/theorems/64e86cee-5ea5-4e4e-a628-a8b15e954dc8
-- title:
--   Edge count of an inclusion-maximal drawable graph for completion
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
