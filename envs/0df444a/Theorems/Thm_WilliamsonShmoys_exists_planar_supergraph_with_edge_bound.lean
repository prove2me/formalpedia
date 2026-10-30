-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_edge_bound
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:08:26.888721+00:00
-- url     : https://prove2.me/theorems/cda78d6a-e134-4fb5-b55a-e8ce11c0fd6f
-- title:
--   Planar graphs have a supergraph meeting the planar edge bound
-- statement:
--   For a finite simple graph drawable in the plane on an ordered vertex type with at least three vertices, there is a drawable supergraph on the same vertices with at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_with_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  sorry
