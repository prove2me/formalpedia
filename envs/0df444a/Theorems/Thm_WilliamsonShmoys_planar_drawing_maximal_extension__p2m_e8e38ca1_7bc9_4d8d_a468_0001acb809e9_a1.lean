-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_e8e38ca1_7bc9_4d8d_a468_0001acb809e9_a1
-- name    : WilliamsonShmoys_planar_drawing_maximal_extension__p2m_e8e38ca1_7bc9_4d8d_a468_0001acb809e9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:40:44.092611+00:00
-- url     : https://prove2.me/theorems/53772a33-25fb-4be5-bc25-56c0a0bf34f9
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on the given vertex set has a drawable supergraph that is maximal among drawable supergraphs on that same vertex set. The finite maximality argument establishes this child; the vertex-count hypothesis is retained from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys_planar_drawing_maximal_extension__p2m_e8e38ca1_7bc9_4d8d_a468_0001acb809e9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by sorry
