-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_extension_maximal_for_same_vertices__p2m_aaf88115_3b68_495f_bd0f_37f00b1cdc73_a1
-- name    : WilliamsonShmoys.exists_planar_extension_maximal_for_same_vertices__p2m_aaf88115_3b68_495f_bd0f_37f00b1cdc73_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:05:33.236433+00:00
-- url     : https://prove2.me/theorems/6b906585-0225-4718-9f11-a92231e3b0bf
-- title:
--   A finite drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   Every finite graph with a crossing-free drawing has an inclusion-maximal drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_extension_maximal_for_same_vertices__p2m_aaf88115_3b68_495f_bd0f_37f00b1cdc73_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by sorry
