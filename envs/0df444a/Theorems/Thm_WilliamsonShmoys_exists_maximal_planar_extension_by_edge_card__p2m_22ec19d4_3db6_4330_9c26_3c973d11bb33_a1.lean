-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_by_edge_card__p2m_22ec19d4_3db6_4330_9c26_3c973d11bb33_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_by_edge_card__p2m_22ec19d4_3db6_4330_9c26_3c973d11bb33_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:32:30.827702+00:00
-- url     : https://prove2.me/theorems/834abd69-ca30-410d-a29d-c379728eedaa
-- title:
--   Finite edge-count maximizer among drawable extensions
-- statement:
--   Among the drawable supergraphs of G on the finite vertex type, one has maximum edge count. The child records a decidable adjacency instance for the chosen graph so its edgeFinset can be counted.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_extension_by_edge_card__p2m_22ec19d4_3db6_4330_9c26_3c973d11bb33_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ (L : SimpleGraph V) (_hLdec : DecidableRel L.Adj),
      G ≤ L ∧
        WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
          G ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H →
            H.edgeFinset.card ≤ L.edgeFinset.card := by sorry
