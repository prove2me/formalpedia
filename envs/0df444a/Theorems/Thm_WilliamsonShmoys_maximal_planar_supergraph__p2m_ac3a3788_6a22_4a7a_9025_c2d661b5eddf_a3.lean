-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_ac3a3788_6a22_4a7a_9025_c2d661b5eddf_a3
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_ac3a3788_6a22_4a7a_9025_c2d661b5eddf_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:24:17.901387+00:00
-- url     : https://prove2.me/theorems/3e1e597e-a255-4249-823e-c2644cc153c4
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion. This removes the finite-choice step from the parent. A proof can maximize the edge set among the finitely many drawable supergraphs containing U; U itself witnesses that the collection is nonempty. The claim also covers graphs with no edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_ac3a3788_6a22_4a7a_9025_c2d661b5eddf_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) :
    ∃ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      HasPlanarDrawingOn W ∧
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       U.edgeFinset ⊆ W.edgeFinset) ∧
      (∀ (X : SimpleGraph V) (dX : DecidableRel X.Adj),
        HasPlanarDrawingOn X →
        (letI : DecidableRel W.Adj := dW
         letI : DecidableRel X.Adj := dX
         W.edgeFinset ⊆ X.edgeFinset) →
        (letI : DecidableRel W.Adj := dW
         letI : DecidableRel X.Adj := dX
         X.edgeFinset ⊆ W.edgeFinset)) := by sorry
