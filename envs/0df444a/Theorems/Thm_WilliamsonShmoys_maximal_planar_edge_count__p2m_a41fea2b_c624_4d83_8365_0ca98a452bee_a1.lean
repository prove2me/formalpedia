-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a41fea2b_c624_4d83_8365_0ca98a452bee_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_a41fea2b_c624_4d83_8365_0ca98a452bee_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:45:31.800866+00:00
-- url     : https://prove2.me/theorems/64c9133b-a623-45e5-bf52-4877372e6864
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite vertices that is maximal among drawable graphs on those vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_a41fea2b_c624_4d83_8365_0ca98a452bee_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ Q : SimpleGraph V,
      (∀ {u v : V}, P.Adj u v → Q.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn Q →
      (∀ {u v : V}, Q.Adj u v → P.Adj u v)) :
    letI : DecidableRel P.Adj := Classical.decRel P.Adj
    P.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
