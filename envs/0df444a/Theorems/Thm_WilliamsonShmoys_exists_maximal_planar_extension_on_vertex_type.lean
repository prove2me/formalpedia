-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_on_vertex_type
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_on_vertex_type
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:15:20.978792+00:00
-- url     : https://prove2.me/theorems/370984e5-5a05-4210-93e4-1d07935f631d
-- title:
--   Every drawable graph has an inclusion-maximal drawable extension
-- statement:
--   Any drawable finite simple graph on a fixed finite vertex type is contained in a drawable graph that has no strictly larger drawable supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension_on_vertex_type
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ H : SimpleGraph V, L ≤ H →
          WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L := by sorry
