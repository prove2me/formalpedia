-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_completion_exact_edge_count__p2m_55144396_2551_4844_a692_ea08946a9a50_a1
-- name    : WilliamsonShmoys.planar_maximal_completion_exact_edge_count__p2m_55144396_2551_4844_a692_ea08946a9a50_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:40:05.27106+00:00
-- url     : https://prove2.me/theorems/e74de359-8181-429e-92f3-9fe027354fb5
-- title:
--   Exact edge count for a planar completion
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. This packages the completion-to-triangulation and Euler-counting work; the parent uses maximality to identify that completion with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_completion_exact_edge_count__p2m_55144396_2551_4844_a692_ea08946a9a50_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    exists K : SimpleGraph V, N <= K /\ HasPlanarDrawingOn K /\
      (letI : DecidableRel K.Adj := Classical.decRel _;
       K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
