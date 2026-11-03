-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:01:27.091553+00:00
-- url     : https://prove2.me/theorems/fd50f30a-a705-4e8f-aa70-6c141aacfb17
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable edge extension on that vertex set has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V,
      (forall u v, M.Adj u v -> N.Adj u v) ->
      HasPlanarDrawingOn N ->
      forall u v, N.Adj u v -> M.Adj u v) :
    letI : forall G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 ≤ M.edgeFinset.card := by
  sorry
