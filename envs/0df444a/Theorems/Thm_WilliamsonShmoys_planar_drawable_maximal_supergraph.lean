-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_supergraph
-- name    : WilliamsonShmoys.planar_drawable_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:45:29.494161+00:00
-- url     : https://prove2.me/theorems/b6b704d1-6906-42d8-842b-85f79f85761d
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite graph is contained in an inclusion-maximal drawable graph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V => L <= M /\ WilliamsonShmoys.HasPlanarDrawingOn M /\
      ∀ N : SimpleGraph V, M <= N → WilliamsonShmoys.HasPlanarDrawingOn N → N <= M := by sorry
