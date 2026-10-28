-- Prove2me | Theorems.Thm_WilliamsonShmoys_extend_planar_drawing_connected_with_linear_edge_additions
-- name    : WilliamsonShmoys.extend_planar_drawing_connected_with_linear_edge_additions
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T20:17:47.601459+00:00
-- url     : https://prove2.me/theorems/d5e8d077-ab2c-43b0-b0c4-95893c04af1d
-- title:
--   Connect a planar drawing with at most |V| added edges
-- statement:
--   Any finite drawable graph with at least three vertices has a connected drawable supergraph on the same vertices, formed by adding at most |V| edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.extend_planar_drawing_connected_with_linear_edge_additions
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    exists H : SimpleGraph V,
      Z.edgeSet ⊆ H.edgeSet ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard <= Z.edgeSet.ncard + Fintype.card V := by sorry
