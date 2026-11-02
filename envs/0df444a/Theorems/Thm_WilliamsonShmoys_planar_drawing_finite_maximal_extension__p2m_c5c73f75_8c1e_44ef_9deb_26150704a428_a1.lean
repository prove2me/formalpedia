-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension__p2m_c5c73f75_8c1e_44ef_9deb_26150704a428_a1
-- name    : WilliamsonShmoys.planar_drawing_finite_maximal_extension__p2m_c5c73f75_8c1e_44ef_9deb_26150704a428_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:35:01.204028+00:00
-- url     : https://prove2.me/theorems/dfccf1a0-d8d5-4c21-b668-467919d5e80f
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable supergraph maximal among drawable supergraphs on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_finite_maximal_extension__p2m_c5c73f75_8c1e_44ef_9deb_26150704a428_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V =>
      And (K <= H) (And (WilliamsonShmoys.HasPlanarDrawingOn H)
        (forall J : SimpleGraph V, H <= J ->
          WilliamsonShmoys.HasPlanarDrawingOn J -> H = J)) := by sorry
