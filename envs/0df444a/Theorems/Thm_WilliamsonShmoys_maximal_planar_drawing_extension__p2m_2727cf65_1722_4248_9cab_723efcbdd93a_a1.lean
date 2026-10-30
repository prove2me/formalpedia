-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_extension__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:48.259964+00:00
-- url     : https://prove2.me/theorems/0e06c23e-290e-423e-a5fe-9ac4288d0e45
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertex type. Choose a drawable supergraph with maximal edge count among the finitely many graphs on the vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_extension__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ (∀ H' : SimpleGraph V, H ≤ H' → H' ≠ H → ¬ HasPlanarDrawingOn H') := by sorry
