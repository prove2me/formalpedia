-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_by_edge_max_e86e41b9
-- name    : WilliamsonShmoys.maximal_drawable_extension_by_edge_max_e86e41b9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:51:52.776177+00:00
-- url     : https://prove2.me/theorems/919e5f59-a5be-4e09-8914-b4a7d6056839
-- title:
--   Existence of a maximal drawable extension by edge count
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_extension_by_edge_max_e86e41b9
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L /\ HasPlanarDrawingOn L /\
        (forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M = L) := by sorry
