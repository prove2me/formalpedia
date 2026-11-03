-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_euler_certificate__p2m_844ee2d0_ef82_4c36_8373_ea0ee656ba91_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_euler_certificate__p2m_844ee2d0_ef82_4c36_8373_ea0ee656ba91_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T13:02:59.482265+00:00
-- url     : https://prove2.me/theorems/e37f737c-f285-4a30-83a0-16b070403a61
-- title:
--   Connected Euler certificate from a planar drawing
-- statement:
--   Given the drawing and at least three vertices, augment G to a connected simple plane graph H on the same vertices, with no fewer edges. Provide a face count satisfying Euler’s equation and the minimum face-length inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_euler_certificate__p2m_844ee2d0_ef82_4c36_8373_ea0ee656ba91_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (f : ℕ),
      G ≤ H ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       G.edgeFinset.card ≤ H.edgeFinset.card) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       Fintype.card V + f = H.edgeFinset.card + 2) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       3 * f ≤ 2 * H.edgeFinset.card) := by sorry
