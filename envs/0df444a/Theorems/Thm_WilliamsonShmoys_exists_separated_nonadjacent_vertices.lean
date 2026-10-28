-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_separated_nonadjacent_vertices
-- name    : WilliamsonShmoys.exists_separated_nonadjacent_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:53:24.816989+00:00
-- url     : https://prove2.me/theorems/c3902cc7-0ca4-43a1-9c0c-0c184c4966c8
-- title:
--   Select vertices in distinct components
-- statement:
--   A disconnected graph with the stated finite vertex type has distinct vertices in different connected components. They are nonadjacent and not reachable from one another. This isolates endpoint selection from the drawing argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_separated_nonadjacent_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ H.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ H.Adj u v ∧ ¬ H.Reachable u v := by sorry
