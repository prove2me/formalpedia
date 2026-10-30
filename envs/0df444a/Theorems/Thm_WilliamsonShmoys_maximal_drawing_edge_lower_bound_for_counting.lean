-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_lower_bound_for_counting
-- name    : WilliamsonShmoys.maximal_drawing_edge_lower_bound_for_counting
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:14:19.591231+00:00
-- url     : https://prove2.me/theorems/4a263b0f-4b5f-4374-821d-b3ca891e3436
-- title:
--   Maximal planar drawing edge lower bound for counting
-- statement:
--   A graph on at least three vertices that is maximal among planar supergraphs on the same vertex set has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_edge_lower_bound_for_counting {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) : 3 * (Fintype.card V : Int) - 6 <= (K.edgeSet.ncard : Int) := by sorry
