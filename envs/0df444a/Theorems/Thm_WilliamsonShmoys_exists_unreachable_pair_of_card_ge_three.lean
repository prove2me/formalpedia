-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair_of_card_ge_three
-- name    : WilliamsonShmoys.exists_unreachable_pair_of_card_ge_three
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:22:23.040986+00:00
-- url     : https://prove2.me/theorems/90570c41-449e-4f42-bf4c-6c97f7ef6c74
-- title:
--   Extract distinct unreachable vertices from a nonconnected graph
-- statement:
--   A nonconnected graph on at least three vertices has two distinct vertices that are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_unreachable_pair_of_card_ge_three
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hnotConnected : ¬ P.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ P.Reachable u v := by sorry
