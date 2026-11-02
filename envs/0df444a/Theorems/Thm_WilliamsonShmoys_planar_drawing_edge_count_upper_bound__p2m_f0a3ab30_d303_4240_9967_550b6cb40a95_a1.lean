-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_f0a3ab30_d303_4240_9967_550b6cb40a95_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_f0a3ab30_d303_4240_9967_550b6cb40a95_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:16.638178+00:00
-- url     : https://prove2.me/theorems/0951cfca-b350-4b14-85c9-9d9dc14f4b38
-- title:
--   Edge upper bound for a finite planar drawing
-- statement:
--   Any finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_f0a3ab30_d303_4240_9967_550b6cb40a95_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 <= Fintype.card V) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    J.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
