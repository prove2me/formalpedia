-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:28:47.071383+00:00
-- url     : https://prove2.me/theorems/1ace3c40-0347-471f-a850-5688ff0e5a6a
-- title:
--   A drawable graph has a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has an inclusion-maximal drawable supergraph on the same vertices. There are finitely many simple graphs on the vertex type, and the original graph makes the set of drawable supergraphs nonempty. This child removes the finite maximal-choice step from the parent; it does not require a lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M ≤ L := by sorry
