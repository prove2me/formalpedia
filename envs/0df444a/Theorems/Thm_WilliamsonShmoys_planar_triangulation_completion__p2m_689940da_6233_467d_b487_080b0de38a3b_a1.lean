-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_689940da_6233_467d_b487_080b0de38a3b_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_689940da_6233_467d_b487_080b0de38a3b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:51:44.460339+00:00
-- url     : https://prove2.me/theorems/2d6ff097-7c5b-40ac-9dcb-907c25524093
-- title:
--   Triangulation completion for a planar drawing
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_689940da_6233_467d_b487_080b0de38a3b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : 3 <= Fintype.card V) :
    ∃ Q : SimpleGraph V,
      (∀ {u v : V}, P.Adj u v → Q.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      (letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
       3 * Fintype.card V = Q.edgeFinset.card + 6) := by sorry
