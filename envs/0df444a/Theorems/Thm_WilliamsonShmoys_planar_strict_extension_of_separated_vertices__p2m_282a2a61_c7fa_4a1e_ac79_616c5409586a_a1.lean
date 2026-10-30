-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_strict_extension_of_separated_vertices__p2m_282a2a61_c7fa_4a1e_ac79_616c5409586a_a1
-- name    : WilliamsonShmoys.planar_strict_extension_of_separated_vertices__p2m_282a2a61_c7fa_4a1e_ac79_616c5409586a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:46:49.391287+00:00
-- url     : https://prove2.me/theorems/281bf234-57f8-455f-a0ca-b7ff75024b61
-- title:
--   Join two separated vertices while preserving a planar drawing
-- statement:
--   Given a crossing-free drawing and vertices in different connected components, add their edge while preserving a crossing-free drawing on the same vertex type. The new adjacency ensures the extension is strict.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_strict_extension_of_separated_vertices__p2m_282a2a61_c7fa_4a1e_ac79_616c5409586a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hplanar : HasPlanarDrawingOn G)
    (u v : V) (hseparated : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ K ≠ G ∧ K.Adj u v ∧ HasPlanarDrawingOn K := by sorry
