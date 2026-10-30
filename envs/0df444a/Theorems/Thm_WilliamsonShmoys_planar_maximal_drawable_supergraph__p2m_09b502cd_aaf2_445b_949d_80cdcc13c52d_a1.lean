-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_drawable_supergraph__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1
-- name    : WilliamsonShmoys.planar_maximal_drawable_supergraph__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:24:20.600893+00:00
-- url     : https://prove2.me/theorems/27628b41-9b86-421c-a9af-b79318367974
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph is contained in a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_drawable_supergraph__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : Exists fun M : SimpleGraph V => Set.Subset H.edgeSet M.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ∀ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
