-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_f0a3ab30_d303_4240_9967_550b6cb40a95_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_f0a3ab30_d303_4240_9967_550b6cb40a95_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:20.085615+00:00
-- url     : https://prove2.me/theorems/78a07d33-949e-45fc-983f-eb458ca767ac
-- title:
--   Edge lower bound for an inclusion-maximal planar drawing
-- statement:
--   An inclusion-maximal finite simple graph with a crossing-free drawing and at least three vertices has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_f0a3ab30_d303_4240_9967_550b6cb40a95_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K -> J <= K -> K <= J)
    (hcard : 3 <= Fintype.card V) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    3 * Fintype.card V - 6 <= J.edgeFinset.card := by sorry
