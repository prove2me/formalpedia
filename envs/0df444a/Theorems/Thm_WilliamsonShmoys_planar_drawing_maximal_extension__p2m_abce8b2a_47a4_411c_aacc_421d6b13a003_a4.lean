-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:25:17.522177+00:00
-- url     : https://prove2.me/theorems/0be9f664-4886-4746-8cb3-c25ee67fb6aa
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   On a finite ordered vertex type, every drawable graph has a drawable supergraph maximal among drawable supergraphs on that type. Choose a drawable supergraph with the largest edge count; any proper supergraph has strictly more edges. This argument also covers types with fewer than three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) :
    ∃ K : SimpleGraph V, M ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
