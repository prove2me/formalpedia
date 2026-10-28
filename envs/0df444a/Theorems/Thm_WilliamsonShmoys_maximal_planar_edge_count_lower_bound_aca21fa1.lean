-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_aca21fa1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_aca21fa1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:16:31.083243+00:00
-- url     : https://prove2.me/theorems/3086c322-8519-4d73-8f33-f085f9c7277b
-- title:
--   Lower edge bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that contains every drawable supergraph on the same vertices has at least \(3|V|-6\) edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_aca21fa1
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : HasPlanarDrawingOn Z)
    (hCard : 3 <= Fintype.card V)
    (hmax : (W : SimpleGraph V) -> HasPlanarDrawingOn W ->
      ((u v : V) -> Z.Adj u v -> W.Adj u v) ->
      (u v : V) -> W.Adj u v -> Z.Adj u v) :
    3 * (Fintype.card V : Int) - 6 <= (Z.edgeSet.ncard : Int) := by sorry
