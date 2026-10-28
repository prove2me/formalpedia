-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_extension_c61b3391
-- name    : WilliamsonShmoys.exists_planar_edge_count_extension_c61b3391
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:55:17.424585+00:00
-- url     : https://prove2.me/theorems/d92f63bc-4bcd-47b5-8ad6-e7c5deb7930d
-- title:
--   Extend a planar drawing to the maximal planar edge count
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_edge_count_extension_c61b3391
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ T : SimpleGraph V,
      K ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
