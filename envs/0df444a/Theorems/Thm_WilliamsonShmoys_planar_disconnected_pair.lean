-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_pair
-- name    : WilliamsonShmoys.planar_disconnected_pair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:40:40.578676+00:00
-- url     : https://prove2.me/theorems/d8d4b3ca-19d7-4c65-8679-fa5a31f7c055
-- title:
--   Find a pair in distinct components
-- statement:
--   A finite graph of cardinality at least three that is not connected has distinct nonadjacent vertices in different connected components. This isolates the finite graph argument from the drawing construction. The cardinality condition rules out the empty-type boundary case; adjacency would itself give reachability. A proof route is to unfold connectedness, obtain an unreachable pair, use the cardinality hypothesis if needed to discharge the empty case, and derive nonadjacency from nonreachability.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_disconnected_pair
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ P.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ P.Adj u v ∧ ¬ P.Reachable u v := by
  sorry
