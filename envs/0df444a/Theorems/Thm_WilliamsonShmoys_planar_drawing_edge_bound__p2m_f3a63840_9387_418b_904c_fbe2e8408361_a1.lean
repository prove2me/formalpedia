-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:18:39.177381+00:00
-- url     : https://prove2.me/theorems/e403ff95-cc05-4f42-b04b-b57aa90cb760
-- title:
--   Edge bound for a connected graph with the specified planar drawing
-- statement:
--   A connected simple graph on at least three vertices with the specified crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconnected : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    letI : (G : SimpleGraph V) → DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
