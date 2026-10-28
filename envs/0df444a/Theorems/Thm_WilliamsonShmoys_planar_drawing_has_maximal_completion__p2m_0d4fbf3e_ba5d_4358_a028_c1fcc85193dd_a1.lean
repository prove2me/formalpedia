-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_completion__p2m_0d4fbf3e_ba5d_4358_a028_c1fcc85193dd_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_completion__p2m_0d4fbf3e_ba5d_4358_a028_c1fcc85193dd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:32:57.124382+00:00
-- url     : https://prove2.me/theorems/355ef174-ddaf-483d-bf6c-18139128965c
-- title:
--   Every drawable graph has a maximal drawable supergraph
-- statement:
--   Any finite drawable simple graph has a drawable supergraph on the same vertices that has no proper drawable supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_completion__p2m_0d4fbf3e_ba5d_4358_a028_c1fcc85193dd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      (∀ G : SimpleGraph V,
        H.edgeSet ⊆ G.edgeSet → HasPlanarDrawingOn G → G.edgeSet = H.edgeSet) := by sorry
