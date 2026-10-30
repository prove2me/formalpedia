-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a7de67a5_633c_46b0_b277_259b7a4818e8_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a7de67a5_633c_46b0_b277_259b7a4818e8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:19:22.192563+00:00
-- url     : https://prove2.me/theorems/dd9d6b7a-9bb5-4d64-bbbe-17ad94ea3598
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is contained in a drawable supergraph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a7de67a5_633c_46b0_b277_259b7a4818e8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) := by sorry
