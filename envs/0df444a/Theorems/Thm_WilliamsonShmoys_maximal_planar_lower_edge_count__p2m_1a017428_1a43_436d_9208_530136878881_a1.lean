-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_edge_count__p2m_1a017428_1a43_436d_9208_530136878881_a1
-- name    : WilliamsonShmoys.maximal_planar_lower_edge_count__p2m_1a017428_1a43_436d_9208_530136878881_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:40:18.071298+00:00
-- url     : https://prove2.me/theorems/3c9e368f-61fd-4a93-9244-4b323cc9e3bc
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has at least 3|V|−6 edges, by extending it to a triangulation and applying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_lower_edge_count__p2m_1a017428_1a43_436d_9208_530136878881_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      (forall {u v : V}, L.Adj u v -> M.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      (forall {u v : V}, M.Adj u v -> L.Adj u v)) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj
     3 * Fintype.card V - 6 <= L.edgeFinset.card) := by sorry
