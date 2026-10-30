-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_edge_bounded_extension_maximal_edge_bound
-- name    : WilliamsonShmoys.planar_graph_has_edge_bounded_extension_maximal_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:46:03.26192+00:00
-- url     : https://prove2.me/theorems/f4cab8f1-36b2-49a4-9100-a8a3956b9d6e
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_edge_bounded_extension_maximal_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hKmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
