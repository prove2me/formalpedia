-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_maximal_extension
-- name    : WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:03:40.864253+00:00
-- url     : https://prove2.me/theorems/e2566476-b6ef-46f0-a10c-8c2f03922eeb
-- title:
--   Finite planar graphs have maximal planar extensions on the same vertices
-- statement:
--   Any finite graph with the packaged planar drawing has an inclusion-maximal planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ T : SimpleGraph V,
      K ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        ∀ U : SimpleGraph V,
          T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by sorry
