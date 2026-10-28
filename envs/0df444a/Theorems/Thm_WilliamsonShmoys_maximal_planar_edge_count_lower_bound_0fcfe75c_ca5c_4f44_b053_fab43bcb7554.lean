-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_0fcfe75c_ca5c_4f44_b053_fab43bcb7554
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_0fcfe75c_ca5c_4f44_b053_fab43bcb7554
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:18:04.480992+00:00
-- url     : https://prove2.me/theorems/febadf1e-9340-457b-8203-939542e79296
-- title:
--   Maximal planar graphs have at least 3n−6 edges
-- statement:
--   An edge-maximal graph under the given drawing predicate, with at least three vertices, has at least 3|V|−6 edges. The proof must derive the triangulation/Euler lower bound for this precise drawing predicate, including disconnected drawings.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_0fcfe75c_ca5c_4f44_b053_fab43bcb7554
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hMax : forall Z : SimpleGraph V,
      HasPlanarDrawingOn Z ->
      (forall u v, Y.Adj u v -> Z.Adj u v) ->
      forall u v, Z.Adj u v -> Y.Adj u v)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= Y.edgeSet.ncard := by sorry
