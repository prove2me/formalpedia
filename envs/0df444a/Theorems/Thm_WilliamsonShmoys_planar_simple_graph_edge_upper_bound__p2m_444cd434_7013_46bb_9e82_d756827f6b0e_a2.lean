-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:19:42.874594+00:00
-- url     : https://prove2.me/theorems/a2ea7bef-e32d-429b-9bbe-071fb272fdb7
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges. Disconnected graphs are included; the bound follows from Euler’s formula and face-edge counting, with components handled by joining them or using the component form of the argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
