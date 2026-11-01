-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count__p2m_89b917c7_2895_4f7d_ae75_caac4f55b041_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count__p2m_89b917c7_2895_4f7d_ae75_caac4f55b041_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:54:31.454831+00:00
-- url     : https://prove2.me/theorems/ed305078-3eca-42b1-9119-6781033ea8fa
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertex set has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count__p2m_89b917c7_2895_4f7d_ae75_caac4f55b041_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hmax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J)
    (dJ : DecidableRel J.Adj)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel J.Adj := dJ;
      J.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
