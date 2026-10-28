-- Prove2me | Theorems.Thm_WilliamsonShmoys_extend_planar_drawing_connected_42ccc764_2657_424e_8d6b_03a01aecd866
-- name    : WilliamsonShmoys.extend_planar_drawing_connected_42ccc764_2657_424e_8d6b_03a01aecd866
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T20:01:27.150833+00:00
-- url     : https://prove2.me/theorems/af68788c-c245-4ed0-bdac-e187db779974
-- title:
--   Connect a planar drawing without adding vertices
-- statement:
--   Extend any drawable graph with at least three vertices to a connected drawable supergraph on the same vertices, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.extend_planar_drawing_connected_42ccc764_2657_424e_8d6b_03a01aecd866
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    exists H : SimpleGraph V,
      Z.edgeSet ⊆ H.edgeSet ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Z.edgeSet.ncard <= H.edgeSet.ncard := by sorry
