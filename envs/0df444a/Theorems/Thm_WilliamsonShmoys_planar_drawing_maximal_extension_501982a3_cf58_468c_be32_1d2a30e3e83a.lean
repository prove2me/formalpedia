-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_501982a3_cf58_468c_be32_1d2a30e3e83a
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_501982a3_cf58_468c_be32_1d2a30e3e83a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:20:22.534755+00:00
-- url     : https://prove2.me/theorems/42a58579-9165-41dc-9918-4c58be90d617
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   A drawable graph on a fixed finite vertex type is contained in a drawable supergraph maximal among drawable supergraphs on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_501982a3_cf58_468c_be32_1d2a30e3e83a
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ K : SimpleGraph V, N ≤ K →
          WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
