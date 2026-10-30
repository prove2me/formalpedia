-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_exists_maximal_supergraph__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
-- name    : WilliamsonShmoys.planar_drawing_exists_maximal_supergraph__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:26:08.407509+00:00
-- url     : https://prove2.me/theorems/e7afab76-b36c-483c-9361-7e3fa4f8788a
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex type that is maximal under edge inclusion. Finiteness permits choosing a candidate with maximum edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_drawing_exists_maximal_supergraph__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ (L : SimpleGraph V) [DecidableRel L.Adj],
        K.edgeFinset ⊆ L.edgeFinset →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeFinset ⊆ K.edgeFinset) := by sorry
