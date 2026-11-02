-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
-- name    : WilliamsonShmoys_planar_connected_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T06:50:21.641863+00:00
-- url     : https://prove2.me/theorems/1d8ffaac-75df-4ce0-8b03-9887c94b1bf3
-- title:
--   Connect a finite planar drawing
-- statement:
--   Every finite planar drawing on a nonempty vertex type can be extended, on the same vertices, to a connected planar graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys_planar_connected_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Connected := by sorry
