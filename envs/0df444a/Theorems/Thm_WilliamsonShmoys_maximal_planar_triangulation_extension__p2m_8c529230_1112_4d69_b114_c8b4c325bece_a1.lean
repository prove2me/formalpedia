-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_8c529230_1112_4d69_b114_c8b4c325bece_a1
-- name    : WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_8c529230_1112_4d69_b114_c8b4c325bece_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:16:58.937308+00:00
-- url     : https://prove2.me/theorems/30b279e4-21a6-4c4d-890c-7937f6bb5764
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing on at least three vertices has a planar supergraph on the same vertex set whose faces are triangular, and hence whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_8c529230_1112_4d69_b114_c8b4c325bece_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V), ∃ (hKdec : DecidableRel K.Adj),
      (∀ u v : V, H.Adj u v → K.Adj u v) ∧
      HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := hKdec; K.edgeFinset.card) + 6 =
        3 * Fintype.card V := by sorry
