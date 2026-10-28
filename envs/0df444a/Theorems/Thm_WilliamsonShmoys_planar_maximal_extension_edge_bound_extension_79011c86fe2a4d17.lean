-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_edge_bound_extension_79011c86fe2a4d17
-- name    : WilliamsonShmoys.planar_maximal_extension_edge_bound_extension_79011c86fe2a4d17
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:54:30.469811+00:00
-- url     : https://prove2.me/theorems/7a0ddc42-42fc-48ee-b37e-e68e97730807
-- title:
--   Finite maximal extension of a planar drawing
-- statement:
--   Every finite graph with the specified planar drawing has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension_edge_bound_extension_79011c86fe2a4d17
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    Exists fun N : SimpleGraph V => M <= N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N <= P →
        WilliamsonShmoys.HasPlanarDrawingOn P → P <= N := by sorry
