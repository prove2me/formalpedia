-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_08c24848_031b_43ea_aa26_092fb49494c8_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_08c24848_031b_43ea_aa26_092fb49494c8_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:05:53.992685+00:00
-- url     : https://prove2.me/theorems/ef7f67a4-b20c-4576-8674-97edcb1c6ef4
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A graph with at least three vertices that has a `HasPlanarDrawingOn` drawing and is maximal among drawable supergraphs on the same vertex type has at least `3|V| - 6` edges. The proof route is to derive connectedness and triangular faces from maximality, then combine Euler’s formula with edge-face incidence counting, including the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_08c24848_031b_43ea_aa26_092fb49494c8_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N = M) :
    (letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
     3 * Fintype.card V - 6 <= M.edgeFinset.card) := by
  sorry
