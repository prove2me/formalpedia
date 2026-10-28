-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_edge_bound_cda78d6a
-- name    : WilliamsonShmoys.maximal_planar_graph_has_edge_bound_cda78d6a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:34:27.037998+00:00
-- url     : https://prove2.me/theorems/1e14dc85-fe67-4e30-934e-c619828dd605
-- title:
--   An inclusion-maximal planar graph has at least three n minus six edges
-- statement:
--   A finite inclusion-maximal simple planar graph on at least three vertices has at least $3n-6$ edges. The vertex-count hypothesis is retained for the edge-bound argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_has_edge_bound_cda78d6a
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDrawing : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  sorry
