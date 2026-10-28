-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_b713f078_5664_4fa1_8fbb_c01b75fa1e9e_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_b713f078_5664_4fa1_8fbb_c01b75fa1e9e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:31:29.099736+00:00
-- url     : https://prove2.me/theorems/02bccae1-cc3c-48e5-a34b-9f4a9988edab
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_b713f078_5664_4fa1_8fbb_c01b75fa1e9e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists (fun H : SimpleGraph V =>
      And (G <= H)
        (And (WilliamsonShmoys.HasPlanarDrawingOn H)
          (forall K : SimpleGraph V,
            H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= H))) := by
  sorry
