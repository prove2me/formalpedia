-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_1794ae85
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_1794ae85
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T15:18:06.575849+00:00
-- url     : https://prove2.me/theorems/c905c6c9-6131-47c2-a1f7-99a3fa0f817e
-- title:
--   Connected drawable supergraph on the same vertices
-- statement:
--   A drawable simple graph on at least three vertices is a subgraph of a connected drawable simple graph on the same vertex type. This isolates the planar topological construction needed to connect distinct drawing components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_1794ae85
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
