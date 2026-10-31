-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1
-- name    : WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:53:59.768408+00:00
-- url     : https://prove2.me/theorems/df73036e-c174-45db-bb7e-bf898419f140
-- title:
--   Edge count of an inclusion-maximal planar drawing
-- statement:
--   An inclusion-maximal simple planar graph on at least three vertices has exactly 3|V| - 6 edges. Maximality here quantifies over all planar supergraphs on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) (hCard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
