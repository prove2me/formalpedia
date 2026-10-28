-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_finite_drawable_supergraph_maximal
-- name    : WilliamsonShmoys.exists_finite_drawable_supergraph_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:49:47.82179+00:00
-- url     : https://prove2.me/theorems/1501d0c6-a39f-4043-b065-8a8e3932496a
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph maximal among drawable supergraphs on that same vertex type. No lower bound on the number of vertices is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_finite_drawable_supergraph_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun T : SimpleGraph V => K <= T /\
      WilliamsonShmoys.HasPlanarDrawingOn T /\
      (∀ U : SimpleGraph V, T <= U →
        WilliamsonShmoys.HasPlanarDrawingOn U → U <= T) := by sorry
