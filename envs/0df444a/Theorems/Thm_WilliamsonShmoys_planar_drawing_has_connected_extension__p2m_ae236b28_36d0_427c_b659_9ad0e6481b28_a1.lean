-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_connected_extension__p2m_ae236b28_36d0_427c_b659_9ad0e6481b28_a1
-- name    : WilliamsonShmoys.planar_drawing_has_connected_extension__p2m_ae236b28_36d0_427c_b659_9ad0e6481b28_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T09:09:55.569721+00:00
-- url     : https://prove2.me/theorems/e12dd832-f69e-4b9b-a032-420a9acf16ce
-- title:
--   Connected planar extension
-- statement:
--   Every finite graph with a crossing-free drawing on its ordered vertex type has a connected supergraph on the same vertices that also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_connected_extension__p2m_ae236b28_36d0_427c_b659_9ad0e6481b28_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ Q.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q := by sorry
