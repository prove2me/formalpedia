-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_extension__p2m_8d9b924c_10a8_4e46_9c92_7f3339daf0a6_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_maximal_extension__p2m_8d9b924c_10a8_4e46_9c92_7f3339daf0a6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:24:07.076837+00:00
-- url     : https://prove2.me/theorems/2e8661d6-fb29-4822-a288-1b10ae7e8a2c
-- title:
--   Finite drawable supergraphs have an inclusion-maximal extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on that same vertex type that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_maximal_extension__p2m_8d9b924c_10a8_4e46_9c92_7f3339daf0a6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N := by sorry
