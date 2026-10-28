-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_augmentation__p2m_8b750c99_2508_4fa0_8f72_2f809c05bba0_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_augmentation__p2m_8b750c99_2508_4fa0_8f72_2f809c05bba0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:42:10.824838+00:00
-- url     : https://prove2.me/theorems/53ad4955-ddc8-46da-8c61-33a0a25dd9ed
-- title:
--   Planar augmentation to the edge bound
-- statement:
--   Every graph with a crossing-free drawing on a finite linearly ordered vertex set of size at least three has a drawable supergraph on that same vertex set with at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_augmentation__p2m_8b750c99_2508_4fa0_8f72_2f809c05bba0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      (∀ u v, R.Adj u v → S.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      3 * Fintype.card V - 6 <= S.edgeSet.ncard := by sorry
