-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_same_vertex_type
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_extension_same_vertex_type
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:05:36.423823+00:00
-- url     : https://prove2.me/theorems/2753cc20-9bc5-4f64-b34f-98e86d8dcac7
-- title:
--   Maximal drawable extension on the same vertex type
-- statement:
--   Every drawable finite simple graph on a fixed finite ordered vertex type has a drawable supergraph on the same type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_maximal_extension_same_vertex_type
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V, Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      ∀ S : SimpleGraph V, R ≤ S →
        WilliamsonShmoys.HasPlanarDrawingOn S → S = R := by sorry
