-- Prove2me | Theorems.Thm_finite_simpleGraph_exists_maximal_supergraph__p2m_ae09d195_ee8e_4c5a_9878_37e9ebede74b_a1
-- name    : finite_simpleGraph_exists_maximal_supergraph__p2m_ae09d195_ee8e_4c5a_9878_37e9ebede74b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:25:19.520469+00:00
-- url     : https://prove2.me/theorems/18d589fc-69b2-4a3f-b36a-3a676ac465a1
-- title:
--   A finite graph property has maximal supergraphs
-- statement:
--   For any property of simple graphs on a finite linearly ordered vertex type, every graph satisfying that property has a property-satisfying supergraph that is maximal under edge inclusion. This removes the finite maximality argument from the parent; a proof can maximize edge count over the finite possibilities for edge sets, then use equality of edge sets to establish equality of graphs. The hypotheses retain the finite vertex type, ordering needed by edgeFinset, and decidability instances needed for edgeFinset. The remaining core is formalizing that finite maximization and the graph extensionality step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem finite_simpleGraph_exists_maximal_supergraph__p2m_ae09d195_ee8e_4c5a_9878_37e9ebede74b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : P G) :
    ∃ (T : SimpleGraph V) (dT : DecidableRel T.Adj),
      P T ∧
      (letI : DecidableRel G.Adj := dG
       letI : DecidableRel T.Adj := dT
       G.edgeFinset ⊆ T.edgeFinset) ∧
      (∀ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
        P U →
        (letI : DecidableRel T.Adj := dT
         letI : DecidableRel U.Adj := dU
         T.edgeFinset ⊆ U.edgeFinset) →
        T = U) := by sorry
