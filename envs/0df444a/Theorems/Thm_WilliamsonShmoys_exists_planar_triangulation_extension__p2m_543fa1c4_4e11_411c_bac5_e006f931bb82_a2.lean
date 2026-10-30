-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension__p2m_543fa1c4_4e11_411c_bac5_e006f931bb82_a2
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension__p2m_543fa1c4_4e11_411c_bac5_e006f931bb82_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:39:17.728699+00:00
-- url     : https://prove2.me/theorems/419df074-7ffa-4f7d-9922-608f3a25f504
-- title:
--   Planar triangulation extension with exact edge count
-- statement:
--   Any finite graph with a crossing-free drawing on at least three vertices extends on the same vertex set to a crossing-free drawing with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_extension__p2m_543fa1c4_4e11_411c_bac5_e006f931bb82_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ H' : SimpleGraph V, H ≤ H' ∧ WilliamsonShmoys.HasPlanarDrawingOn H' ∧ 3 * Fintype.card V - 6 = H'.edgeSet.ncard := by sorry
