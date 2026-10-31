-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:44:47.14516+00:00
-- url     : https://prove2.me/theorems/3cbfa21b-87e9-46ce-9a05-e9f44cd63dc5
-- title:
--   Extend a drawable graph to an inclusion maximal drawable graph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex type that is inclusion maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by sorry
