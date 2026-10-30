-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_euler_20261027
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_euler_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:07:54.586984+00:00
-- url     : https://prove2.me/theorems/1e52d5d6-6b79-46ff-829f-42b3b7201237
-- title:
--   Exact edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable edge-supergraph on the same vertex type has exactly 3|V|−6 edges. The proof must establish the triangulation and Euler-counting argument for the supplied drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_euler_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : forall R : SimpleGraph V,
      (forall {u v}, Q.Adj u v -> R.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn R -> R = Q)
    (hV : 3 <= Fintype.card V) :
    Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
