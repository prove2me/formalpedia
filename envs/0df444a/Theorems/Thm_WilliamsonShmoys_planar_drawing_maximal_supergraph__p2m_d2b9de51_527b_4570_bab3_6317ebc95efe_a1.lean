-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_d2b9de51_527b_4570_bab3_6317ebc95efe_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_d2b9de51_527b_4570_bab3_6317ebc95efe_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:24:32.942402+00:00
-- url     : https://prove2.me/theorems/673ae955-532e-446b-aa2e-918e7755fe58
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal under edge inclusion among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_d2b9de51_527b_4570_bab3_6317ebc95efe_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V,
        N.edgeSet ⊆ P.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn P →
        P.edgeSet = N.edgeSet := by sorry
