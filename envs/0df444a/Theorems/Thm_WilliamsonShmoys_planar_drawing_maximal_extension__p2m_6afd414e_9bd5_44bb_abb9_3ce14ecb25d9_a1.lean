-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_6afd414e_9bd5_44bb_abb9_3ce14ecb25d9_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6afd414e_9bd5_44bb_abb9_3ce14ecb25d9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:48:04.048601+00:00
-- url     : https://prove2.me/theorems/d861cb11-4d1d-4208-9ad9-8ec6eefefc53
-- title:
--   Extend a planar drawing to a maximal planar supergraph
-- statement:
--   Any graph with the supplied crossing-free drawing, on at least three vertices, has a planar supergraph on the same vertices that is maximal under adding edges while preserving planarity. The statement also provides decidability for the supergraph’s adjacency so its edge finset is available.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6afd414e_9bd5_44bb_abb9_3ce14ecb25d9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, ∃ (_ : DecidableRel H.Adj),
      G.edgeFinset ⊆ H.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  sorry
