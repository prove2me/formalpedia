-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2f35ea45_99df_4cf1_95b2_81f89b32ddea_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_2f35ea45_99df_4cf1_95b2_81f89b32ddea_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:50:32.958251+00:00
-- url     : https://prove2.me/theorems/34ce151f-05d3-497c-a88f-b630e2f0d090
-- title:
--   Maximal planar graphs have the triangulation edge count
-- statement:
--   A finite graph with at least three vertices that is maximal among planar supergraphs on the same vertex type has exactly 3|V|−6 edges. The proof route is to show maximality forces every face of a planar drawing to be triangular, then combine 3|F|=2|E| with Euler’s formula |V|−|E|+|F|=2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_2f35ea45_99df_4cf1_95b2_81f89b32ddea_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hn : 3 <= Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel _
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
