-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound
-- name    : WilliamsonShmoys.planar_supergraph_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:06:11.556667+00:00
-- url     : https://prove2.me/theorems/69665468-de5a-4b4d-b03f-2970a33b710f
-- title:
--   Planar supergraph edge bound on the same vertices
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_bound {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ 3 * Fintype.card V - 6 <= L.edgeSet.ncard := by sorry
