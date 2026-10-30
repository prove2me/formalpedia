-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_lower_bound_v2
-- name    : WilliamsonShmoys.maximal_planar_drawing_triangulation_lower_bound_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:33:28.687162+00:00
-- url     : https://prove2.me/theorems/eb0d732d-d4fa-4cbb-94d7-ceb6f42a4af4
-- title:
--   Lower edge bound from maximal planarity
-- statement:
--   A connected simple planar graph on at least three vertices that is maximal among planar supergraphs on the same vertex set has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_triangulation_lower_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
