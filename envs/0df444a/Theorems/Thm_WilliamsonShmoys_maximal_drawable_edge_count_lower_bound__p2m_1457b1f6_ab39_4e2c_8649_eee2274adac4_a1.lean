-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_1457b1f6_ab39_4e2c_8649_eee2274adac4_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_1457b1f6_ab39_4e2c_8649_eee2274adac4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:31:34.30021+00:00
-- url     : https://prove2.me/theorems/f6fd06f3-0c3f-4439-84c7-1bb602bf038f
-- title:
--   Maximal drawable graphs meet the planar edge lower bound
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has at least 3|V|−6 edges. Triangulating the drawing gives a drawable supergraph with that many edges, which maximality identifies with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_1457b1f6_ab39_4e2c_8649_eee2274adac4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdraw : HasPlanarDrawingOn N)
    (hmax : forall H : SimpleGraph V,
      (forall u v, N.Adj u v -> H.Adj u v) ->
      HasPlanarDrawingOn H -> H = N) :
    letI : forall H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    3 * Fintype.card V - 6 <= N.edgeFinset.card := by sorry
