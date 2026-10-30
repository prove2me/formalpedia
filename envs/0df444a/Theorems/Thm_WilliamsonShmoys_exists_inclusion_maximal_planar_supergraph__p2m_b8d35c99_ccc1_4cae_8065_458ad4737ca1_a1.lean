-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_b8d35c99_ccc1_4cae_8065_458ad4737ca1_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_b8d35c99_ccc1_4cae_8065_458ad4737ca1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:57:23.46832+00:00
-- url     : https://prove2.me/theorems/fbbb88e7-37d9-449e-b606-8639662290f5
-- title:
--   Every finite drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertex set that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_b8d35c99_ccc1_4cae_8065_458ad4737ca1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    Exists fun M : SimpleGraph V => G <= M /\ HasPlanarDrawingOn M /\
      ∀ N : SimpleGraph V, M <= N → HasPlanarDrawingOn N → N = M := by
  sorry
