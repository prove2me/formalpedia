-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_c643eab9_16cc_4e69_8d73_dd1e68fa5bd2_a2
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_c643eab9_16cc_4e69_8d73_dd1e68fa5bd2_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:06:44.22289+00:00
-- url     : https://prove2.me/theorems/58dc5ab1-94a9-407e-bf9a-7b232f0762ef
-- title:
--   Finite maximal planar extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices whose edge set is maximal by inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension__p2m_c643eab9_16cc_4e69_8d73_dd1e68fa5bd2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W) :
    letI : DecidableRel W.Adj := Classical.decRel W.Adj
    ∃ H : SimpleGraph V, HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       W.edgeFinset ⊆ H.edgeFinset) ∧
      ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
        (letI : DecidableRel H.Adj := Classical.decRel H.Adj
         letI : DecidableRel K.Adj := Classical.decRel K.Adj
         H.edgeFinset ⊆ K.edgeFinset → K.edgeFinset ⊆ H.edgeFinset) := by sorry
