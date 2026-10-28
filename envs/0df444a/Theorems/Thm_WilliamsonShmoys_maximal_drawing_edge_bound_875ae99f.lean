-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_bound_875ae99f
-- name    : WilliamsonShmoys.maximal_drawing_edge_bound_875ae99f
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:42:57.238126+00:00
-- url     : https://prove2.me/theorems/e3322ee4-770e-467a-82df-15d112e9cf23
-- title:
--   Lower edge bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph has at least $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_edge_bound_875ae99f
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by sorry
