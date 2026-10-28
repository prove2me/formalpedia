-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_50a3c5c3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_50a3c5c3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:38:24.176691+00:00
-- url     : https://prove2.me/theorems/83af1d5e-c8f0-4d3c-abf0-2c1fc152afa7
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly 3n−6 edges. The proof obligation is the topological maximal-planar edge-count result: establish connectedness and triangular faces from maximality, then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_50a3c5c3
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hCard : 3 ≤ Fintype.card V)
    (hQmax : ∀ R : SimpleGraph V,
      Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R ≤ Q) :
    Q.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
