-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_triangulation_count__p2m_1625d03f_5f98_459a_8070_43608692433f_a2
-- name    : WilliamsonShmoys.planar_supergraph_with_triangulation_count__p2m_1625d03f_5f98_459a_8070_43608692433f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:12:14.723205+00:00
-- url     : https://prove2.me/theorems/b79a3d22-514c-40c6-b0d9-3192cd4e6368
-- title:
--   Planar augmentation with the triangulation edge count
-- statement:
--   Any drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_with_triangulation_count__p2m_1625d03f_5f98_459a_8070_43608692433f_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hK : HasPlanarDrawingOn K) (hcard : 3 ≤ Fintype.card V) : ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj), K ≤ L ∧ HasPlanarDrawingOn L ∧ 3 * Fintype.card V = L.edgeFinset.card + 6 := by sorry
