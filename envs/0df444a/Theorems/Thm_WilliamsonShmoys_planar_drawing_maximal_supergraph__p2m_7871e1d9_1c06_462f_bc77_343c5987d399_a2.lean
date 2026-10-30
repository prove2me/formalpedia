-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:37:51.431407+00:00
-- url     : https://prove2.me/theorems/c6944f63-e851-4122-bc82-20fe0d441b4b
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on a fixed vertex set has a drawable supergraph maximal under edge inclusion. There are only finitely many simple graphs on that vertex set, so one can choose a drawable supergraph with the largest edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ H : SimpleGraph V, M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = M := by sorry
