-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_maximal_drawable__p2m_1d9e4996_f1da_4af7_951a_5adb0b1eb381_a1
-- name    : WilliamsonShmoys.planar_edge_count_of_maximal_drawable__p2m_1d9e4996_f1da_4af7_951a_5adb0b1eb381_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T09:17:11.697733+00:00
-- url     : https://prove2.me/theorems/0391e42c-80e1-4784-8f6b-41c1d2f81516
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable finite simple graph with at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_of_maximal_drawable__p2m_1d9e4996_f1da_4af7_951a_5adb0b1eb381_a1 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hP : HasPlanarDrawingOn P) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ Q : SimpleGraph V, Set.Subset P.edgeSet Q.edgeSet → HasPlanarDrawingOn Q → Set.Subset Q.edgeSet P.edgeSet) : P.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
