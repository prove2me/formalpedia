-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_b94a5187
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_b94a5187
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:59:34.642908+00:00
-- url     : https://prove2.me/theorems/8a462a45-0eb4-4feb-94c6-30f44c2696b4
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph on that same vertex type which is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_b94a5187
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V,
        H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H := by sorry
