-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_f2cfae8b_743a_4350_8c03_fa33aa7b455e_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_f2cfae8b_743a_4350_8c03_fa33aa7b455e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:16:14.887419+00:00
-- url     : https://prove2.me/theorems/36795df0-a9ab-414e-b2f3-447339417680
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_f2cfae8b_743a_4350_8c03_fa33aa7b455e_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hmax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L = K) (hcard : 3 <= Fintype.card V) : (letI : DecidableRel K.Adj := Classical.decRel K.Adj; 3 * Fintype.card V - 6 <= K.edgeFinset.card) := by sorry
