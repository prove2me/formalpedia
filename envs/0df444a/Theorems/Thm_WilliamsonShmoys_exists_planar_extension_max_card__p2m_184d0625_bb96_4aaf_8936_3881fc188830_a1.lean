-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_extension_max_card__p2m_184d0625_bb96_4aaf_8936_3881fc188830_a1
-- name    : WilliamsonShmoys.exists_planar_extension_max_card__p2m_184d0625_bb96_4aaf_8936_3881fc188830_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:43:06.426025+00:00
-- url     : https://prove2.me/theorems/0a52e576-3c89-4eab-a8d4-2aab6ce01438
-- title:
--   Planar extension maximizing edge count
-- statement:
--   Among the planar supergraphs of a given finitely supported graph on the same vertex type, there is one whose edge count is at least that of every other such supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_extension_max_card__p2m_184d0625_bb96_4aaf_8936_3881fc188830_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
        ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
          K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
