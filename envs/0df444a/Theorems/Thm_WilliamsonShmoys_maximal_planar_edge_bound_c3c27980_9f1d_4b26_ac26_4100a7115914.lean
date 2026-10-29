-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_c3c27980_9f1d_4b26_ac26_4100a7115914
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_c3c27980_9f1d_4b26_ac26_4100a7115914
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:32:41.642993+00:00
-- url     : https://prove2.me/theorems/22946254-5952-4266-8a27-d37e80c91a91
-- title:
--   Edge bound for maximal planar graphs
-- statement:
--   A graph with the specified planar drawing that admits no proper drawing-preserving supergraph on the same vertex type has at most three times its number of vertices minus six edges, provided it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound_c3c27980_9f1d_4b26_ac26_4100a7115914
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
