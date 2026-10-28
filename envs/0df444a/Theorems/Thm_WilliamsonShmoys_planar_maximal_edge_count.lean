-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count
-- name    : WilliamsonShmoys.planar_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:29:07.171779+00:00
-- url     : https://prove2.me/theorems/aca21fa1-6cf3-41a4-be05-cf434d24b440
-- title:
--   Drawable supergraph with the planar edge bound
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable supergraph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hCard : 3 <= Fintype.card V) :
    ∃ Z : SimpleGraph V,
      HasPlanarDrawingOn Z ∧
      (∀ u v, Y.Adj u v → Z.Adj u v) ∧
      (Z.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
