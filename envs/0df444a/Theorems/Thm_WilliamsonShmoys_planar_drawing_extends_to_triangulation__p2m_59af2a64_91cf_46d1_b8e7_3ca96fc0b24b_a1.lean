-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_triangulation__p2m_59af2a64_91cf_46d1_b8e7_3ca96fc0b24b_a1
-- name    : WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_59af2a64_91cf_46d1_b8e7_3ca96fc0b24b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:23:47.782369+00:00
-- url     : https://prove2.me/theorems/6b272625-9d5c-443e-9411-b56416706ef1
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Every drawable finite simple graph on at least three ordered vertices is an edge-subgraph of a drawable triangulation on the same vertex set, with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_59af2a64_91cf_46d1_b8e7_3ca96fc0b24b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (dT : DecidableRel T.Adj)
    (hT : HasPlanarDrawingOn T)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
      HasPlanarDrawingOn U ∧
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset ⊆ U.edgeFinset) ∧
      (letI : DecidableRel U.Adj := dU
       U.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
