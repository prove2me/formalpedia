-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_same_vertex_edge_maximal_planar_extension
-- name    : WilliamsonShmoys.exists_same_vertex_edge_maximal_planar_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:36:27.003378+00:00
-- url     : https://prove2.me/theorems/a6368dfd-2084-498a-aa3f-a8abc105dc2c
-- title:
--   Maximal drawable extension on the same vertex type
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_same_vertex_edge_maximal_planar_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by sorry
