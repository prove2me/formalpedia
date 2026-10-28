-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_connectedExtension
-- name    : WilliamsonShmoys.planarDrawing_connectedExtension
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T04:55:03.711561+00:00
-- url     : https://prove2.me/theorems/1de335d9-a990-4e8a-8ab6-9008241e1dd3
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Any finite graph with a crossing-free drawing has a connected supergraph on the same vertices that also has a crossing-free drawing. This removes disconnected-component handling from the parent and is proved by joining embedded components through the complement while preserving the original arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_connectedExtension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      K.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
