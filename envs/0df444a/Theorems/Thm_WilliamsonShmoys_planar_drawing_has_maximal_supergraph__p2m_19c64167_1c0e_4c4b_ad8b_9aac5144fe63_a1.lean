-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_19c64167_1c0e_4c4b_ad8b_9aac5144fe63_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_19c64167_1c0e_4c4b_ad8b_9aac5144fe63_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:20:26.075248+00:00
-- url     : https://prove2.me/theorems/ae09d195-ee8e-4c5a-9878-37e9ebede74b
-- title:
--   Extend a drawable graph to an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has an inclusion-maximal drawable supergraph on the same vertices. The maximality is among all drawable supergraphs on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_19c64167_1c0e_4c4b_ad8b_9aac5144fe63_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    ∃ (T : SimpleGraph V) (dT : DecidableRel T.Adj),
      HasPlanarDrawingOn T ∧
      (letI : DecidableRel G.Adj := dG
       letI : DecidableRel T.Adj := dT
       G.edgeFinset ⊆ T.edgeFinset) ∧
      (∀ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
        HasPlanarDrawingOn U →
        (letI : DecidableRel T.Adj := dT
         letI : DecidableRel U.Adj := dU
         T.edgeFinset ⊆ U.edgeFinset) →
        T = U) := by sorry
