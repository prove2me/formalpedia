-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_card_of_inclusion_maximal_planar__p2m_bf9cfcbc_5b59_49b9_abb2_d36aa9cb22f2_a1
-- name    : WilliamsonShmoys.edge_card_of_inclusion_maximal_planar__p2m_bf9cfcbc_5b59_49b9_abb2_d36aa9cb22f2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:20:24.795645+00:00
-- url     : https://prove2.me/theorems/6fea05f3-38bb-4c39-a43f-259b933c0070
-- title:
--   Edge count of an inclusion-maximal planar drawing
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing, on at least three vertices, has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_card_of_inclusion_maximal_planar__p2m_bf9cfcbc_5b59_49b9_abb2_d36aa9cb22f2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card) = 3 * Fintype.card V - 6 := by sorry
