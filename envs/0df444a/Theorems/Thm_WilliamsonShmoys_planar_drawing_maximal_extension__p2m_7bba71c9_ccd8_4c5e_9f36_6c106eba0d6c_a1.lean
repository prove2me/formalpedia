-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_7bba71c9_ccd8_4c5e_9f36_6c106eba0d6c_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_7bba71c9_ccd8_4c5e_9f36_6c106eba0d6c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:31:21.62745+00:00
-- url     : https://prove2.me/theorems/9e1ef792-7281-4f22-9d2f-56978c7b0370
-- title:
--   Maximal drawable extension on the same vertices
-- statement:
--   Every finite connected drawable graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs, with at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_7bba71c9_ccd8_4c5e_9f36_6c106eba0d6c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hconn : N.Connected) (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     ∃ H : SimpleGraph V, N ≤ H ∧ HasPlanarDrawingOn H ∧
       (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
       (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
        N.edgeFinset.card ≤ H.edgeFinset.card)) := by
  sorry
