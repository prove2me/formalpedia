-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:05:16.325605+00:00
-- url     : https://prove2.me/theorems/8cd0804a-f792-4057-bb92-319536b24856
-- title:
--   Every drawable finite graph has an inclusion-maximal drawable supergraph
-- statement:
--   On a fixed finite vertex set, choose a drawable graph containing G with the largest possible edge set. Finiteness of the candidate graph family gives an inclusion-maximal choice. This removes the extension-existence step from the parent; a proof can encode candidate edge sets as a finite family and take a maximum. No vertex-count lower bound is needed here.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by sorry
