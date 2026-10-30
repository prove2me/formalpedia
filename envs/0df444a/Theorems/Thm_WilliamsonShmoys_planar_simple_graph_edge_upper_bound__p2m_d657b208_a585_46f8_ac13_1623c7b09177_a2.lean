-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:13:10.659243+00:00
-- url     : https://prove2.me/theorems/57c3e2f0-3143-4ad3-84d0-92c0d48df09b
-- title:
--   Edge upper bound for a finite simple planar graph
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The size hypothesis is needed for the usual planar bound in this exact form.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    G.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
