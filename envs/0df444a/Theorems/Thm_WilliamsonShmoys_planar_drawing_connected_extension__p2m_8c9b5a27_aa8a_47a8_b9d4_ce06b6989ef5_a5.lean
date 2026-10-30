-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:07:08.931026+00:00
-- url     : https://prove2.me/theorems/eb36caad-992c-4412-9250-64661542f0e2
-- title:
--   Connected planar supergraph on the same vertices
-- statement:
--   A finite drawn graph on at least three vertices can be extended, without adding vertices or removing edges, to a connected graph with a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    ∃ K' : SimpleGraph V,
      K'.Connected ∧
      HasPlanarDrawingOn K' ∧
      K.edgeSet.ncard <= K'.edgeSet.ncard := by sorry
