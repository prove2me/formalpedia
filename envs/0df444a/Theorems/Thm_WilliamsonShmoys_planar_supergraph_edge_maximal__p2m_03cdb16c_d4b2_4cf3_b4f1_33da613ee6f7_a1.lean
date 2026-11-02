-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_maximal__p2m_03cdb16c_d4b2_4cf3_b4f1_33da613ee6f7_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_maximal__p2m_03cdb16c_d4b2_4cf3_b4f1_33da613ee6f7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:28:27.399174+00:00
-- url     : https://prove2.me/theorems/f754c05e-6809-4cce-be14-e23de7f7dc38
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Among the planar supergraphs of a finite planar graph on the same vertex type, there is one whose edge count is at least that of every other planar supergraph. The proof uses finiteness of the simple graphs on the vertex type; the original graph supplies a candidate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_maximal__p2m_03cdb16c_d4b2_4cf3_b4f1_33da613ee6f7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, M ≤ K → HasPlanarDrawingOn K →
        (letI : DecidableRel K.Adj := Classical.decRel K.Adj
         letI : DecidableRel N.Adj := Classical.decRel N.Adj
         K.edgeFinset.card ≤ N.edgeFinset.card) := by sorry
