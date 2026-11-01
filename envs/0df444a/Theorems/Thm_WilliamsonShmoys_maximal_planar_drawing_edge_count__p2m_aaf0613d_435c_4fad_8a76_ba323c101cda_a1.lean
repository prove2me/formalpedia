-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_aaf0613d_435c_4fad_8a76_ba323c101cda_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_aaf0613d_435c_4fad_8a76_ba323c101cda_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:15:54.725436+00:00
-- url     : https://prove2.me/theorems/29b19c22-dee0-4e68-89b3-79c840e8be72
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_aaf0613d_435c_4fad_8a76_ba323c101cda_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
