-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:29:51.205831+00:00
-- url     : https://prove2.me/theorems/b230c174-4dc5-4f1c-a300-93827e81df10
-- title:
--   Every drawable finite graph has a drawable maximal extension
-- statement:
--   Any drawable graph on a finite ordered vertex type has a drawable supergraph maximal among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = K := by sorry
