-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_maximal_supergraph__p2m_c063ecbf_b4be_428e_95f9_2de36a0b9a32_a1
-- name    : WilliamsonShmoys.planar_augmentation_maximal_supergraph__p2m_c063ecbf_b4be_428e_95f9_2de36a0b9a32_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T23:06:41.075748+00:00
-- url     : https://prove2.me/theorems/aaefc2cb-8b36-4190-b672-a3768c07fc94
-- title:
--   Extend a drawable graph to an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has an inclusion-maximal drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_maximal_supergraph__p2m_c063ecbf_b4be_428e_95f9_2de36a0b9a32_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    exists K : SimpleGraph V,
      H <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
        forall L : SimpleGraph V, K <= L ->
          WilliamsonShmoys.HasPlanarDrawingOn L -> L = K := by
  sorry
