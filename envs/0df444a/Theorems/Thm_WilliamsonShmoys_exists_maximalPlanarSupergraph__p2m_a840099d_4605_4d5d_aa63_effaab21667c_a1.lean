-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximalPlanarSupergraph__p2m_a840099d_4605_4d5d_aa63_effaab21667c_a1
-- name    : WilliamsonShmoys.exists_maximalPlanarSupergraph__p2m_a840099d_4605_4d5d_aa63_effaab21667c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:24:49.11409+00:00
-- url     : https://prove2.me/theorems/bf821f48-a839-4428-8d3d-0233762c650a
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Any finite drawable simple graph has a drawable supergraph on the same vertices that is maximal under drawable edge-set inclusion. This removes the extension-existence step from the parent. An independent route is to maximize the finite edge count among drawable supergraphs containing the given graph; a strictly larger drawable supergraph would contradict maximality. No vertex-count lower bound is needed for this lemma.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximalPlanarSupergraph__p2m_a840099d_4605_4d5d_aa63_effaab21667c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      HasPlanarDrawingOn L ∧
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel L.Adj := dL
       K.edgeFinset ⊆ L.edgeFinset) ∧
      (∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
        HasPlanarDrawingOn M →
        (letI : DecidableRel L.Adj := dL
         letI : DecidableRel M.Adj := dM
         L.edgeFinset ⊆ M.edgeFinset) →
        (letI : DecidableRel L.Adj := dL
         letI : DecidableRel M.Adj := dM
         L.edgeFinset = M.edgeFinset)) := by sorry
