-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists__p2m_89b917c7_2895_4f7d_ae75_caac4f55b041_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_89b917c7_2895_4f7d_ae75_caac4f55b041_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:54:31.185572+00:00
-- url     : https://prove2.me/theorems/e34d7a09-23ce-4570-8dfd-e776462a4233
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Any drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_89b917c7_2895_4f7d_ae75_caac4f55b041_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ J : SimpleGraph V,
      G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧
        ∀ K : SimpleGraph V,
          J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J := by sorry
