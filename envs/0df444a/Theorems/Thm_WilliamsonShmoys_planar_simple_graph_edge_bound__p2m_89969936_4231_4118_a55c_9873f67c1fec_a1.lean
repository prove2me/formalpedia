-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_89969936_4231_4118_a55c_9873f67c1fec_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_89969936_4231_4118_a55c_9873f67c1fec_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:13:54.140602+00:00
-- url     : https://prove2.me/theorems/ae2deb14-265a-4589-b20a-d2c312b9c2e6
-- title:
--   Edge bound for a drawable simple graph
-- statement:
--   A simple graph with a crossing-free drawing on a finite linearly ordered vertex type has at most 3|V|−6 edges when |V|≥3. The condition includes the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_89969936_4231_4118_a55c_9873f67c1fec_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn G) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
