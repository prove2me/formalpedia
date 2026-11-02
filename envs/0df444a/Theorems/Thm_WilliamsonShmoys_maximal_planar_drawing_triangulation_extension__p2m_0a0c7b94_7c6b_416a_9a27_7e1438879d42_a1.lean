-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_extension__p2m_0a0c7b94_7c6b_416a_9a27_7e1438879d42_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_0a0c7b94_7c6b_416a_9a27_7e1438879d42_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:05:22.56106+00:00
-- url     : https://prove2.me/theorems/dee0ca40-6c9c-434d-8ef7-a3ab7a09b0fc
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Every finite drawable simple graph on at least three vertices is contained in a drawable graph on the same vertices whose edges satisfy the planar triangulation count 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_0a0c7b94_7c6b_416a_9a27_7e1438879d42_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hR : HasPlanarDrawingOn R) :
    ∃ T : SimpleGraph V, R ≤ T ∧ HasPlanarDrawingOn T ∧
      (letI : DecidableRel T.Adj := Classical.decRel T.Adj
       3 * Fintype.card V = T.edgeFinset.card + 6) := by sorry
