-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulated_edge_count__p2m_1ccfbc5e_ee72_4561_8bb6_ab9cee0a3a68_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangulated_edge_count__p2m_1ccfbc5e_ee72_4561_8bb6_ab9cee0a3a68_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:53:02.58972+00:00
-- url     : https://prove2.me/theorems/18bbe9c1-8b0d-4062-b19f-3ec33678fcd4
-- title:
--   A maximal drawable simple graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no strict drawable supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangulated_edge_count__p2m_1ccfbc5e_ee72_4561_8bb6_ab9cee0a3a68_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
