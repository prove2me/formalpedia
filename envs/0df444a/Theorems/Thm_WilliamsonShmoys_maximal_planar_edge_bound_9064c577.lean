-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_9064c577
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_9064c577
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:24:58.835327+00:00
-- url     : https://prove2.me/theorems/3a5dc006-b6d3-4515-9d19-ce21b43c29f8
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A connected simple graph that is maximal among drawable supergraphs on its vertex type has at most 3|V|−6 edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_bound_9064c577
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hConn : K.Connected)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V,
      (∀ ⦃u v⦄, K.Adj u v → L.Adj u v) →
      HasPlanarDrawingOn L →
      ∀ ⦃u v⦄, L.Adj u v → K.Adj u v) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
