-- Prove2me | Theorems.Thm_WilliamsonShmoys_extract_one_edge_from_drawable_extension
-- name    : WilliamsonShmoys.extract_one_edge_from_drawable_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:55:31.467857+00:00
-- url     : https://prove2.me/theorems/9cc39e16-c6de-48a4-ae97-9be3ae2f6e82
-- title:
--   Extract a drawable one-edge intermediate
-- statement:
--   If a drawable finite simple graph strictly extends another graph on the same vertex type, the smaller graph has a drawable supergraph with exactly one additional edge. Finiteness lets the strict edge-set inclusion supply an edge to add; the larger graph’s drawing supplies the drawing for the intermediate graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.extract_one_edge_from_drawable_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hneq : G ≠ H) :
    ∃ J : SimpleGraph V,
      G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = G.edgeSet.ncard + 1 := by
  sorry
