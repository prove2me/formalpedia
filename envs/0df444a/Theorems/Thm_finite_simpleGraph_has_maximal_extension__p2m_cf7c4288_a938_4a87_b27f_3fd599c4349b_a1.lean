-- Prove2me | Theorems.Thm_finite_simpleGraph_has_maximal_extension__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1
-- name    : finite_simpleGraph_has_maximal_extension__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:18:47.108752+00:00
-- url     : https://prove2.me/theorems/194803d5-8f3d-46b7-b09f-175284d76087
-- title:
--   Finite edge-removal-closed properties have maximal extensions
-- statement:
--   For any property of simple graphs on a finite ordered vertex type that is preserved when edges are removed, every graph satisfying it is contained in a satisfying graph with no strictly larger satisfying supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem finite_simpleGraph_has_maximal_extension__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃G H : SimpleGraph V⦄, H.edgeSet ⊆ G.edgeSet → P G → P H)
    (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ P K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → P L →
        L.edgeSet ⊆ K.edgeSet := by sorry
