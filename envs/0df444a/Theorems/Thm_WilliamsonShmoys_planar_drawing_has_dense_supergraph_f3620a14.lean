-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_dense_supergraph_f3620a14
-- name    : WilliamsonShmoys.planar_drawing_has_dense_supergraph_f3620a14
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:21:56.609054+00:00
-- url     : https://prove2.me/theorems/b78c43d7-3644-4a9d-a128-52043bc8bb14
-- title:
--   Dense drawable supergraph for the maximal drawing edge bound
-- statement:
--   Every drawable graph on at least three vertices has a drawable supergraph on the same vertices with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_dense_supergraph_f3620a14
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      S ≤ R ∧
      3 * Fintype.card V - 6 ≤ R.edgeSet.ncard := by sorry
