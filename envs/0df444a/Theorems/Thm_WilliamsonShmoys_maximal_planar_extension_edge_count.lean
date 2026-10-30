-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count
-- name    : WilliamsonShmoys.maximal_planar_extension_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T07:00:48.284742+00:00
-- url     : https://prove2.me/theorems/0d153890-30e1-4032-9b45-090ce37fbb88
-- title:
--   Triangulated extension of a planar drawing
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. The case |V|=3 is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
