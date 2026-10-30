-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_extension_to_connected__p2m_50dbeb3a_1765_4569_965c_952b7ed019cf_a2
-- name    : WilliamsonShmoys.finite_simpleGraph_extension_to_connected__p2m_50dbeb3a_1765_4569_965c_952b7ed019cf_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:09:34.312256+00:00
-- url     : https://prove2.me/theorems/bc1dbe68-8ab3-415d-b271-02c22c1992c4
-- title:
--   Finite strict extensions reach a connected graph
-- statement:
--   On a finite vertex type, if a property-preserving strict edge extension exists for every disconnected graph satisfying the property, then every graph satisfying the property has a connected supergraph that also satisfies it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_simpleGraph_extension_to_connected__p2m_50dbeb3a_1765_4569_965c_952b7ed019cf_a2
    {V : Type} [Fintype V] (H : SimpleGraph V)
    (P : SimpleGraph V → Prop) (hP : P H)
    (hstep : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ K : SimpleGraph V, G.edgeSet ⊂ K.edgeSet ∧ P K) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ P K ∧ K.Connected := by sorry
