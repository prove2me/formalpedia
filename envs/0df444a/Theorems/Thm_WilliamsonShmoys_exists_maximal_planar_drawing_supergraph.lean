-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:04:57.168829+00:00
-- url     : https://prove2.me/theorems/f216c728-e43a-4fcc-b853-7846b85e2d16
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every finite graph with a drawing has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_drawing_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
