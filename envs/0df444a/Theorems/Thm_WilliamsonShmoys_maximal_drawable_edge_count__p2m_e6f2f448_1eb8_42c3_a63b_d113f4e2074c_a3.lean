-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_e6f2f448_1eb8_42c3_a63b_d113f4e2074c_a3
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_e6f2f448_1eb8_42c3_a63b_d113f4e2074c_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:17:49.29124+00:00
-- url     : https://prove2.me/theorems/126577ef-f856-473b-b1f2-d55f4854fb26
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertex type has exactly `3n−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_e6f2f448_1eb8_42c3_a63b_d113f4e2074c_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj
     K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
