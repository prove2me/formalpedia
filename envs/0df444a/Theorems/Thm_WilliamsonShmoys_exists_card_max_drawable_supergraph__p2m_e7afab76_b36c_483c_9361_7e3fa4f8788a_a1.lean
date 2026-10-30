-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_card_max_drawable_supergraph__p2m_e7afab76_b36c_483c_9361_7e3fa4f8788a_a1
-- name    : WilliamsonShmoys.exists_card_max_drawable_supergraph__p2m_e7afab76_b36c_483c_9361_7e3fa4f8788a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:47:37.898835+00:00
-- url     : https://prove2.me/theorems/340f9e76-64f2-48e1-9fcc-1c693aa1e5eb
-- title:
--   A drawable supergraph with maximum edge count
-- statement:
--   Among the drawable supergraphs of H on the same finite vertex type, there is one whose edge set has maximum cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.exists_card_max_drawable_supergraph__p2m_e7afab76_b36c_483c_9361_7e3fa4f8788a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ (L : SimpleGraph V) [DecidableRel L.Adj],
        H.edgeFinset ⊆ L.edgeFinset →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeFinset.card ≤ K.edgeFinset.card) := by sorry
