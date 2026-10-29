-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_edge_bound_373dcc1c_b5a0_431f_b2a4_dc3190258bf0
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension_edge_bound_373dcc1c_b5a0_431f_b2a4_dc3190258bf0
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:49:15.248874+00:00
-- url     : https://prove2.me/theorems/f39f88bf-8625-48f9-b44c-01764ef15f8d
-- title:
--   Extend a drawable graph to a triangulated drawable supergraph
-- statement:
--   For a finite linearly ordered vertex type with at least three elements, every graph with a crossing-free drawing has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. The hypothesis |V|≥3 includes the three-vertex boundary case and makes the stated natural-number subtraction meaningful.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_extension_edge_bound_373dcc1c_b5a0_431f_b2a4_dc3190258bf0
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
