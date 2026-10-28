-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_density
-- name    : WilliamsonShmoys.planar_completion_density
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:49:01.33314+00:00
-- url     : https://prove2.me/theorems/3cae4d70-0f9f-4904-982d-afebb02eb77f
-- title:
--   Planar graphs admit a dense planar completion
-- statement:
--   Every planar simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a planar graph on the same vertices whose edge count is at least three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_density
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, HasPlanarDrawingOn L ∧
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
