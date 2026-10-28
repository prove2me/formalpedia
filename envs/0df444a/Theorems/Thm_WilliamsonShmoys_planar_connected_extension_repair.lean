-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension_repair
-- name    : WilliamsonShmoys.planar_connected_extension_repair
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T04:53:46.696123+00:00
-- url     : https://prove2.me/theorems/4cb5386b-d06a-47f6-b291-00c6c14857de
-- title:
--   Connected drawable extension on the same vertex set
-- statement:
--   A finite drawable graph with at least three vertices has a connected drawable supergraph on the same vertex set whose edge count is at least the original’s. One proof route connects drawing components through the complement while retaining the original vertices and arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_extension_repair
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard <= H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
