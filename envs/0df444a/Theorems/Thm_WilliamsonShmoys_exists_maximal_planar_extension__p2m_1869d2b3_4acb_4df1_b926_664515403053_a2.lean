-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_1869d2b3_4acb_4df1_b926_664515403053_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_1869d2b3_4acb_4df1_b926_664515403053_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:16:05.222865+00:00
-- url     : https://prove2.me/theorems/cf08a975-8aa0-46e9-901e-a88c02c5eb25
-- title:
--   Finite maximal planar extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that admits no proper drawable supergraph, and the original graph has no more edges. Choose an edge-maximizing graph among the finitely many drawable supergraphs of H. Edge inclusion gives the cardinality inequality; maximal edge count rules out any proper drawable extension. This removes finite augmentation and edge bookkeeping from the parent. The remaining core obligation is the maximal planar edge bound in the second child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_1869d2b3_4acb_4df1_b926_664515403053_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ u v, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        ∀ u v, L.Adj u v → K.Adj u v) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       H.edgeFinset.card ≤ K.edgeFinset.card) := by sorry
