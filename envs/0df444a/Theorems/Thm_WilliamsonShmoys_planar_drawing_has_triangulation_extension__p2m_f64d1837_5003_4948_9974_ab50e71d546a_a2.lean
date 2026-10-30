-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_extension__p2m_f64d1837_5003_4948_9974_ab50e71d546a_a2
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation_extension__p2m_f64d1837_5003_4948_9974_ab50e71d546a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:05:25.527911+00:00
-- url     : https://prove2.me/theorems/f5f2a8b8-a8d9-45a6-8446-39002bc3ddba
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing on an ordered vertex type of size at least three is a subgraph of a crossing-free triangulation on the same vertex type, with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulation_extension__p2m_f64d1837_5003_4948_9974_ab50e71d546a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : LE.le 3 (Fintype.card V)) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
