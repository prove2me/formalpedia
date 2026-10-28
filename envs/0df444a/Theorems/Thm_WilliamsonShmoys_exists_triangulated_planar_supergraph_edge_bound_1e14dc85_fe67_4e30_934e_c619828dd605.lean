-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph_edge_bound_1e14dc85_fe67_4e30_934e_c619828dd605
-- name    : WilliamsonShmoys.exists_triangulated_planar_supergraph_edge_bound_1e14dc85_fe67_4e30_934e_c619828dd605
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:26:14.593437+00:00
-- url     : https://prove2.me/theorems/cbc0594c-ac31-4402-82bd-76ff29091572
-- title:
--   Extend a finite planar drawing to a triangulated planar supergraph
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulated_planar_supergraph_edge_bound_1e14dc85_fe67_4e30_934e_c619828dd605
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDrawing : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  sorry
